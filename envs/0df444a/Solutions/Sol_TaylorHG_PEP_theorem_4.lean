-- Prove2me | solution 1 for TaylorHG.PEP.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T09:49:39.614262+00:00
-- url     : https://prove2.me/submissions/5d91b169-c425-4407-8bda-54f640cb2245

-- Direction: Alexander Richard Towell (queelius); proof and verification: OpenAI Codex.
-- Mathematics: Adrien B. Taylor, Julien M. Hendrickx, François Glineur, arXiv1502.05666v6.
-- Platform: mikedeng1, Shuze Chen; shared subgradient interface credits N. Z. Shor.
-- Complete smooth strongly convex interpolation equivalence in the platform real-valued class.
-- No claim of mathematical novelty or independent human review.
-- Includes actual convex/strong conjugate construction, Hahn-Banach subgradient existence,
-- differentiability, sharp quadratic upper bounds, and finite/infinite-L necessity.
import Mathlib
import Definitions.Def_TaylorHG_PEP_Interp
set_option autoImplicit false
open TaylorHG.PEP
namespace ConvexInterpolation
lemma class_zero {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) : FClass 0 ⊤ f := by
  refine ⟨hf,?_,?_⟩
  · intro x y g h _ _
    simp only [ENNReal.inv_top,ENNReal.toReal_zero,zero_mul]
    exact norm_nonneg _
  · simpa only [NNReal.coe_zero,zero_div,zero_mul,sub_zero] using hf
end ConvexInterpolation

theorem convex_interpolation {d : ℕ} {ι : Type*} [Fintype ι]
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable 0 ⊤ x g fv ↔
      ∀ i j, fv j + inner ℝ (g j) (x i - x j) ≤ fv i := by
  classical
  constructor
  · rintro ⟨f,hf,hi⟩ i j
    have h := (hi j).2 (x i)
    rw [(hi i).1,(hi j).1] at h
    linarith
  · intro h
    cases isEmpty_or_nonempty ι with
    | inl he =>
      letI := he
      exact ⟨fun _ => 0,ConvexInterpolation.class_zero _ (convexOn_const _ convex_univ),fun i => isEmptyElim i⟩
    | inr he =>
      letI := he
      let A := fun (j : ι) (z : EuclideanSpace ℝ (Fin d)) => fv j+inner ℝ (g j) (z-x j)
      let f := fun z => ⨆ j, A j z
      have hbound (z) : BddAbove (Set.range (fun j => A j z)) := (Set.finite_range _).bddAbove
      have hle (j z) : A j z ≤ f z := le_ciSup (hbound z) j
      have hf : ConvexOn ℝ Set.univ f := by
        refine ⟨convex_univ,?_⟩
        intro u _ v _ a b ha hb hab
        apply ciSup_le
        intro j
        have hu := mul_le_mul_of_nonneg_left (hle j u) ha
        have hv := mul_le_mul_of_nonneg_left (hle j v) hb
        have heq : A j (a • u+b • v)=a*A j u+b*A j v := by
          dsimp [A]
          simp only [inner_sub_right,inner_add_right,inner_smul_right]
          have heq : b=1-a := by linarith
          rw [heq]
          ring
        rw [heq]
        exact add_le_add hu hv
      have hval (i) : f (x i)=fv i := by
        apply le_antisymm
        · exact ciSup_le (fun j => h i j)
        · have hi := hle i (x i)
          simpa only [A,sub_self,inner_zero_right,add_zero] using hi
      refine ⟨f,ConvexInterpolation.class_zero f hf,?_⟩
      intro i
      refine ⟨hval i,?_⟩
      intro z
      have hi := hle i z
      rw [hval i]
      dsimp [A] at hi
      linarith
namespace ConvexInterpolation
lemma small_quadratic (D c : ℝ) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t*D+c*t^2) : 0 ≤ D := by
  by_contra hn
  have hD := lt_of_not_ge hn
  let m := min 1 (-D)
  let t := m/(2*(c+1))
  have hm : 0 < m := lt_min (by norm_num) (by linarith)
  have hd : 0 < 2*(c+1) := by linarith
  have ht : 0 < t := div_pos hm hd
  have he : 2*(c+1)*t=m := mul_div_cancel₀ _ (ne_of_gt hd)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmD : m ≤ -D := min_le_right _ _
  have ht1 : t ≤ 1 := by nlinarith [mul_nonneg hc ht.le]
  have hb := h t ht ht1
  have hx : 0 ≤ D+c*t := (mul_nonneg_iff_of_pos_left ht).mp (by nlinarith [hb])
  nlinarith
lemma quadratic_expand {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖x+t • v‖^2=‖x‖^2+2*t*inner ℝ x v+t^2*‖v‖^2 := by
  rw [norm_add_sq_real,inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  ring
lemma shift_subgradient {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hc : ConvexOn ℝ Set.univ (fun z => f z-m/2*‖z‖^2))
    (x g : EuclideanSpace ℝ (Fin d)) :
    ShorNonsmooth.AlmostDiff.IsSubgradient f x g ↔
      ShorNonsmooth.AlmostDiff.IsSubgradient (fun z => f z-m/2*‖z‖^2) x (g-m • x) := by
  constructor
  · intro hg z
    let v := z-x
    let D := f z-m/2*‖z‖^2-(f x-m/2*‖x‖^2)-inner ℝ (g-m • x) (z-x)
    apply sub_nonneg.mp
    change 0 ≤ D
    apply small_quadratic D (m/2*‖v‖^2) (mul_nonneg (by linarith) (sq_nonneg _))
    intro t ht ht1
    have he : (1-t) • x+t • z=x+t • v := by dsimp [v];module
    have hconv := hc.2 (Set.mem_univ x) (Set.mem_univ z) (sub_nonneg.mpr ht1) ht.le
      (show 1-t+t=1 by ring)
    rw [he] at hconv
    have hsub := hg (x+t • v)
    have hvec : x+t • v-x=t • v := by module
    rw [hvec,inner_smul_right] at hsub
    have hnorm := quadratic_expand x v t
    have hnormZ : ‖z‖^2=‖x‖^2+2*inner ℝ x v+‖v‖^2 := by
      have hz : z=x+v := by dsimp [v];module
      conv_lhs => rw [hz]
      exact norm_add_sq_real x v
    have hinner : inner ℝ (g-m • x) (z-x)=inner ℝ g v-m*inner ℝ x v := by
      simp [v,inner_sub_left,inner_smul_left]
    dsimp only at hconv
    simp only [smul_eq_mul] at hconv
    dsimp only [D]
    rw [hinner]
    rw [hnorm] at hconv
    nlinarith [hconv,hsub]
  · intro hg z
    have hz := hg z
    have hnorm := norm_sub_sq_real z x
    have hmnorm := mul_nonneg hm (sq_nonneg ‖z-x‖)
    simp [inner_sub_left,inner_smul_left,inner_sub_right,real_inner_self_eq_norm_sq] at hz
    rw [real_inner_comm] at hnorm
    have hweighted := congrArg (fun q : ℝ => m*q) hnorm
    simp only [inner_sub_right]
    nlinarith
end ConvexInterpolation
namespace ConvexInterpolation
lemma add_quadratic_convex {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (hc : ConvexOn ℝ Set.univ h) (m : ℝ) (hm : 0 ≤ m) :
    ConvexOn ℝ Set.univ (fun z => h z+m/2*‖z‖^2) := by
  have hnorm : ConvexOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖^2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  exact hc.add (hnorm.smul (by linarith : 0 ≤ m/2))
lemma curvature_interpolation {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable μ ⊤ x g fv ↔
      Interpolable 0 ⊤ x (fun i => g i-(μ : ℝ) • x i)
        (fun i => fv i-(μ : ℝ)/2*‖x i‖^2) := by
  constructor
  · rintro ⟨f,hF,hi⟩
    refine ⟨fun z => f z-(μ : ℝ)/2*‖z‖^2,class_zero _ hF.2.2,?_⟩
    intro i
    refine ⟨by dsimp only; rw [(hi i).1],(shift_subgradient f μ μ.coe_nonneg hF.2.2 (x i) (g i)).mp (hi i).2⟩
  · rintro ⟨h,hF,hi⟩
    let f := fun z => h z+(μ : ℝ)/2*‖z‖^2
    have hshift : ConvexOn ℝ Set.univ (fun z => f z-(μ : ℝ)/2*‖z‖^2) := by
      simpa only [f,add_sub_cancel_right] using hF.1
    have hclass : FClass μ ⊤ f := by
      refine ⟨add_quadratic_convex h hF.1 μ μ.coe_nonneg,?_,hshift⟩
      intro a b ga gb _ _
      simp only [ENNReal.inv_top,ENNReal.toReal_zero,zero_mul]
      exact norm_nonneg _
    refine ⟨f,hclass,?_⟩
    intro i
    refine ⟨?_,(shift_subgradient f μ μ.coe_nonneg hshift (x i) (g i)).mpr ?_⟩
    · dsimp [f]
      rw [(hi i).1]
      ring
    · simpa only [f,add_sub_cancel_right] using (hi i).2
lemma strong_interpolation {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable μ ⊤ x g fv ↔ ∀ i j, InterpIneq μ ⊤ x g fv i j := by
  rw [curvature_interpolation,convex_interpolation]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  have hn := norm_sub_sq_real (x i) (x j)
  rw [real_inner_comm] at hn
  have hm := congrArg (fun q : ℝ => (μ : ℝ)*q) hn
  simp [InterpIneq,inner_sub_left,inner_smul_left,inner_sub_right] at *
  constructor <;> intro h <;> nlinarith
end ConvexInterpolation
namespace ConvexInterpolation
open ShorNonsmooth.AlmostDiff Filter
open scoped Topology
lemma strong_support {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hc : ConvexOn ℝ Set.univ (fun z => f z-m/2*‖z‖^2))
    {x g : EuclideanSpace ℝ (Fin d)} (hg : IsSubgradient f x g) (z : EuclideanSpace ℝ (Fin d)) :
    f x+inner ℝ g (z-x)+m/2*‖z-x‖^2 ≤ f z := by
  have h := (shift_subgradient f m hm hc x g).mp hg z
  simp only [inner_sub_left,inner_smul_left,inner_sub_right,real_inner_self_eq_norm_sq,starRingEnd_apply,star_trivial] at h
  have hn := norm_sub_sq_real z x
  rw [real_inner_comm] at hn
  have hw := congrArg (fun a : ℝ => m/2*a) hn
  simp only [inner_sub_right]
  nlinarith
lemma strong_mono {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hc : ConvexOn ℝ Set.univ (fun z => f z-m/2*‖z‖^2))
    {x y gx gy : EuclideanSpace ℝ (Fin d)} (hx : IsSubgradient f x gx) (hy : IsSubgradient f y gy) :
    m*‖x-y‖ ≤ ‖gx-gy‖ := by
  have h1 := strong_support f m hm hc hx y
  have h2 := strong_support f m hm hc hy x
  have hi : inner ℝ (gx-gy) (x-y) ≤ ‖gx-gy‖*‖x-y‖ := real_inner_le_norm _ _
  simp only [inner_sub_left,inner_sub_right] at hi h1 h2
  rw [norm_sub_rev y x] at h1
  by_cases hn : ‖x-y‖=0
  · rw [hn,mul_zero];exact norm_nonneg _
  · have hp : 0 < ‖x-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    nlinarith
lemma conjugate_exists {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f)
    (m a : ℝ) (hm : 0 < m) (b : EuclideanSpace ℝ (Fin d))
    (hlower : ∀ z,a+inner ℝ b z+m/2*‖z‖^2 ≤ f z) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ y,∀ z, inner ℝ x z-f z ≤ inner ℝ x y-f y := by
  have hcont : Continuous (fun z => f z-inner ℝ x z) := hf.sub (continuous_const.inner continuous_id)
  have hlim : Tendsto (fun z => f z-inner ℝ x z) (cocompact _) atTop := by
    apply tendsto_atTop.2
    intro c
    let D := |a|+|c|+1
    let B := ‖b-x‖
    let R := max 1 (2*(B+D)/m)
    filter_upwards [(tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin d))).eventually_ge_atTop R] with z hz
    have hR1 : 1 ≤ R := le_max_left _ _
    have hR2 : 2*(B+D)/m ≤ R := le_max_right _ _
    have hquad : 2*(B+D) ≤ m*‖z‖ := by
      have h := (div_le_iff₀ hm).mp (hR2.trans hz)
      nlinarith
    have hlow := hlower z
    have hinner : -B*‖z‖ ≤ inner ℝ (b-x) z := by
      have hi := real_inner_le_norm (-(b-x)) z
      simpa only [inner_neg_left,norm_neg,neg_neg,neg_mul,B] using (neg_le_neg hi)
    simp only [inner_sub_left] at hinner
    have ha := neg_abs_le a
    have hc := le_abs_self c
    have hD : 0 < D := by dsimp [D];positivity
    have hnorm : 1 ≤ ‖z‖ := hR1.trans hz
    have hmul := mul_nonneg (sub_nonneg.mpr hquad) (norm_nonneg z)
    dsimp [D] at hD
    dsimp [D] at hmul
    nlinarith [mul_nonneg (by dsimp [D];positivity : 0 ≤ D) (sub_nonneg.mpr hnorm)]
  obtain ⟨y,hy⟩ := hcont.exists_forall_le hlim
  exact ⟨y,fun z => by have h:=hy z;linarith⟩

lemma smooth_conjugate {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ) (hm : 0 < m)
    (hc : ConvexOn ℝ Set.univ (fun z => f z-m/2*‖z‖^2))
    (hex : ∀ x : EuclideanSpace ℝ (Fin d),∃ y,∀ z,inner ℝ x z-f z ≤ inner ℝ x y-f y) :
    ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ConvexOn ℝ Set.univ h ∧
      (∀ x y,IsSubgradient f y x → h x=inner ℝ x y-f y ∧ IsSubgradient h x y) ∧
      (∀ x y gx gy,IsSubgradient h x gx → IsSubgradient h y gy → m*‖gx-gy‖ ≤ ‖x-y‖) := by
  classical
  choose w hw using hex
  let h := fun x => inner ℝ x (w x)-f (w x)
  have hsub (x) : IsSubgradient f (w x) x := by
    intro z
    have hz := hw x z
    simp only [inner_sub_right]
    linarith
  have hLip (x y) : m*‖w x-w y‖ ≤ ‖x-y‖ := strong_mono f m hm.le hc (hsub x) (hsub y)
  have hlower (x z) : h x+inner ℝ (w x) (z-x) ≤ h z := by
    have hz := hw z (w x)
    dsimp [h]
    have he : inner ℝ (w x) (z-x)=inner ℝ (z-x) (w x) := real_inner_comm _ _
    rw [he,inner_sub_left]
    linarith
  have hupper (x z) : h z ≤ h x+inner ℝ (w x) (z-x)+(1/(2*m))*‖z-x‖^2 := by
    have hs := strong_support f m hm.le hc (hsub x) (w z)
    have hin : inner ℝ (z-x) (w z-w x) ≤ ‖z-x‖*‖w z-w x‖ := real_inner_le_norm _ _
    have hsquare : 0 ≤ (‖z-x‖-m*‖w z-w x‖)^2 := sq_nonneg _
    have hid : inner ℝ z (w z)-inner ℝ x (w x)-inner ℝ (w x) (z-x) =
      inner ℝ x (w z-w x)+inner ℝ (z-x) (w z-w x) := by
      simp only [inner_sub_left,inner_sub_right]
      rw [real_inner_comm (w x) z,real_inner_comm (w x) x]
      ring
    have hd : 0 < 2*m := by positivity
    apply (mul_le_mul_iff_of_pos_right hd).mp
    have hdiv : (h x+inner ℝ (w x) (z-x)+(1/(2*m))*‖z-x‖^2)*(2*m)=
      (inner ℝ x (w x)-f (w x)+inner ℝ (w x) (z-x))*(2*m)+‖z-x‖^2 := by dsimp [h];field_simp
    rw [hdiv]
    dsimp [h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hm.le,mul_nonneg (sub_nonneg.mpr hin) hm.le]
  have hgrad (x gx) (hg : IsSubgradient h x gx) : gx=w x := by
    have hzero : 0 ≤ -‖gx-w x‖^2 := by
      apply small_quadratic _ ((1/(2*m))*‖gx-w x‖^2) (by positivity)
      intro t ht ht1
      have hu := hupper x (x+t • (gx-w x))
      have hl := hg (x+t • (gx-w x))
      have he : x+t • (gx-w x)-x=t • (gx-w x) := by module
      rw [he,inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] at hu
      rw [he,inner_smul_right] at hl
      have hh := real_inner_self_eq_norm_sq (gx-w x)
      simp only [inner_sub_left] at hh
      nlinarith
    have hz : ‖gx-w x‖=0 := by nlinarith [norm_nonneg (gx-w x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  refine ⟨h,?_,?_,?_⟩
  · refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    have hx := hw x (w (a • x+b • y))
    have hy := hw y (w (a • x+b • y))
    dsimp [h]
    simp only [inner_add_left,inner_smul_left,smul_eq_mul,starRingEnd_apply,star_trivial]
    have hh := congrArg (fun t : ℝ => t*f (w (a • x+b • y))) hab
    simp only [one_mul] at hh
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx),mul_nonneg hb (sub_nonneg.mpr hy)]
  · intro x y hy
    have hyw : y=w x := by
      have hh := strong_mono f m hm.le hc hy (hsub x)
      simp only [sub_self,norm_zero] at hh
      have hz : ‖y-w x‖=0 := by nlinarith [norm_nonneg (y-w x)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    subst y
    exact ⟨rfl,fun z => by have hz:=hlower x z;linarith⟩
  · intro x y gx gy hx hy
    rw [hgrad x gx hx,hgrad y gy hy]
    exact hLip x y
end ConvexInterpolation
namespace ConvexInterpolation
open ShorNonsmooth.AlmostDiff
lemma conjugate_exists_of_support {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ) (hm : 0 < m)
    (hf : ConvexOn ℝ Set.univ f) (hc : ConvexOn ℝ Set.univ (fun z => f z-m/2*‖z‖^2))
    (y g : EuclideanSpace ℝ (Fin d)) (hg : IsSubgradient f y g) :
    ∀ x : EuclideanSpace ℝ (Fin d),∃ z,∀ u,inner ℝ x u-f u ≤ inner ℝ x z-f z := by
  have hcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  apply conjugate_exists f hcont m (f y-inner ℝ g y+m/2*‖y‖^2) hm (g-m • y)
  intro z
  have h := strong_support f m hm.le hc hg z
  have hn := norm_sub_sq_real z y
  rw [real_inner_comm] at hn
  have hw := congrArg (fun a : ℝ => m/2*a) hn
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,starRingEnd_apply,star_trivial] at *
  nlinarith
lemma constant_class {d : ℕ} (L : ENNReal) : FClass 0 L (fun _ : EuclideanSpace ℝ (Fin d) => 0) := by
  have hz (x g : EuclideanSpace ℝ (Fin d)) (hg : IsSubgradient (fun _ => (0 : ℝ)) x g) : g=0 := by
    have h := hg (x+g)
    simp only [add_sub_cancel_left,sub_self,real_inner_self_eq_norm_sq] at h
    have hn : ‖g‖=0 := by nlinarith [norm_nonneg g]
    exact norm_eq_zero.mp hn
  refine ⟨convexOn_const _ convex_univ,?_,?_⟩
  · intro x y gx gy hx hy
    rw [hz x gx hx,hz y gy hy]
    simp
  · simpa using (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin d)))))
lemma smooth_sufficiency {d : ℕ} {ι : Type*} [Fintype ι]
    (L : ℝ) (hL : 0 < L) (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ)
    (hdata : ∀ i j, (1/(2*L))*‖g i-g j‖^2 ≤ fv i-fv j-inner ℝ (g j) (x i-x j)) :
    Interpolable 0 (ENNReal.ofReal L) x g fv := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    letI := hi
    exact ⟨fun _ => 0,constant_class _,fun i => isEmptyElim i⟩
  | inr hi =>
    letI := hi
    let m : NNReal := ⟨1/L,by positivity⟩
    have hmcoe : (m : ℝ)=1/L := rfl
    let fvD := fun i => inner ℝ (x i) (g i)-fv i
    have hD : ∀ i j,InterpIneq m ⊤ g x fvD i j := by
      intro i j
      have hh := hdata j i
      have hn : ‖g j-g i‖=‖g i-g j‖ := norm_sub_rev _ _
      rw [hn] at hh
      simp only [InterpIneq,ENNReal.inv_top,ENNReal.toReal_zero,mul_zero,zero_mul,sub_zero,
        one_div_one,zero_add,one_mul] 
      rw [hmcoe]
      dsimp [fvD]
      simp only [inner_sub_right]
      simp only [inner_sub_right] at hh
      rw [real_inner_comm (g i) (x i),real_inner_comm (g j) (x j),real_inner_comm (g i) (x j)]
      convert hh using 1 <;> (try field_simp) <;> ring
    obtain ⟨f,hf,hfi⟩ := (strong_interpolation m g x fvD).mpr hD
    let i0 : ι := Classical.choice hi
    have hm : 0 < (m : ℝ) := by rw [hmcoe];positivity
    have hex := conjugate_exists_of_support f m hm hf.1 hf.2.2 (g i0) (x i0) (hfi i0).2
    obtain ⟨h,hconv,hdual,hlip⟩ := smooth_conjugate f m hm hf.2.2 hex
    refine ⟨h,⟨hconv,?_,?_⟩,?_⟩
    · intro a b ga gb ha hb
      have hh := hlip a b ga gb ha hb
      rw [hmcoe] at hh
      simpa only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hL.le,one_div] using hh
    · simpa only [NNReal.coe_zero,zero_div,zero_mul,sub_zero] using hconv
    · intro i
      obtain ⟨hv,hg⟩ := hdual (x i) (g i) (hfi i).2
      refine ⟨?_,hg⟩
      rw [(hfi i).1] at hv
      dsimp [fvD] at hv
      linarith
end ConvexInterpolation

namespace ConvexInterpolation
open ShorNonsmooth.AlmostDiff
lemma shifted_data {d : ℕ} {ι : Type*} (μ : NNReal) (L : ℝ) (hL : (μ:ℝ) < L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ)
    (hdata : ∀ i j, InterpIneq μ (ENNReal.ofReal L) x g fv i j) :
    ∀ i j, (1/(2*(L-μ)))*‖(g i-(μ:ℝ) • x i)-(g j-(μ:ℝ) • x j)‖^2 ≤
      (fv i-(μ:ℝ)/2*‖x i‖^2)-(fv j-(μ:ℝ)/2*‖x j‖^2)-
        inner ℝ (g j-(μ:ℝ) • x j) (x i-x j) := by
  intro i j
  have hLp : 0 < L := lt_of_le_of_lt μ.coe_nonneg hL
  have hd : 0 < 1-(μ:ℝ)/L := by apply sub_pos.mpr;exact (div_lt_one hLp).mpr hL
  have hi := hdata i j
  simp only [InterpIneq,ENNReal.toReal_inv,ENNReal.toReal_ofReal hLp.le] at hi
  have hi' := (mul_le_mul_iff_of_pos_left (show 0 < 2*(1-(μ:ℝ)*L⁻¹) by simpa [div_eq_mul_inv] using mul_pos (by norm_num : (0:ℝ)<2) hd)).mpr hi
  have hn : ‖(g i-(μ:ℝ) • x i)-(g j-(μ:ℝ) • x j)‖^2 =
      ‖g i-g j‖^2-2*(μ:ℝ)*inner ℝ (g i-g j) (x i-x j)+(μ:ℝ)^2*‖x i-x j‖^2 := by
    have he : (g i-(μ:ℝ) • x i)-(g j-(μ:ℝ) • x j) = (g i-g j)-(μ:ℝ) • (x i-x j) := by module
    rw [he,norm_sub_sq_real,inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    ring
  have hx := norm_sub_sq_real (x i) (x j)
  have hinner : inner ℝ (g j-g i) (x j-x i) = inner ℝ (g i-g j) (x i-x j) := by
    rw [← neg_sub (g i) (g j),← neg_sub (x i) (x j),inner_neg_left,inner_neg_right,neg_neg]
  rw [hinner] at hi'
  have hLne : L ≠ 0 := ne_of_gt hLp
  have hden : 2*(1-(μ:ℝ)*L⁻¹) ≠ 0 := by positivity
  field_simp [hden,ne_of_gt (sub_pos.mpr hL)] at hi'
  apply (mul_le_mul_iff_of_pos_left (show 0 < 2*(L-μ) by positivity)).mp
  rw [hn]
  field_simp [ne_of_gt (sub_pos.mpr hL)]
  simp only [inner_sub_left,inner_smul_left,inner_sub_right,real_inner_self_eq_norm_sq,starRingEnd_apply,star_trivial] at *
  rw [← real_inner_comm (x i) (x j)] at hx
  have hw := congrArg (fun q : ℝ => (μ:ℝ)*(L-μ)*q) hx
  simp only [mul_div_cancel_left₀ _ (ne_of_gt (sub_pos.mpr hL))] at hi' ⊢
  nlinarith
lemma finite_strong_sufficiency {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (L : ℝ) (hL : (μ:ℝ) < L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ)
    (hdata : ∀ i j, InterpIneq μ (ENNReal.ofReal L) x g fv i j) :
    Interpolable μ (ENNReal.ofReal L) x g fv := by
  have hmL : 0 < L-(μ:ℝ) := sub_pos.mpr hL
  have hLp : 0 < L := lt_of_le_of_lt μ.coe_nonneg hL
  obtain ⟨h,hF,hi⟩ := smooth_sufficiency (L-μ) hmL x (fun i => g i-(μ:ℝ) • x i)
    (fun i => fv i-(μ:ℝ)/2*‖x i‖^2) (shifted_data μ L hL x g fv hdata)
  let f := fun z => h z+(μ:ℝ)/2*‖z‖^2
  have hshift : ConvexOn ℝ Set.univ (fun z => f z-(μ:ℝ)/2*‖z‖^2) := by
    simpa only [f,add_sub_cancel_right] using hF.1
  refine ⟨f,⟨add_quadratic_convex h hF.1 μ μ.coe_nonneg,?_,hshift⟩,?_⟩
  · intro a b ga gb ha hb
    have hga := (shift_subgradient f μ μ.coe_nonneg hshift a ga).mp ha
    have hgb := (shift_subgradient f μ μ.coe_nonneg hshift b gb).mp hb
    simp only [f,add_sub_cancel_right] at hga hgb
    have hlip := hF.2.1 a b (ga-(μ:ℝ) • a) (gb-(μ:ℝ) • b) hga hgb
    simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hmL.le] at hlip
    have hbnd : ‖(ga-(μ:ℝ) • a)-(gb-(μ:ℝ) • b)‖ ≤ (L-μ)*‖a-b‖ := by
      have hh := mul_le_mul_of_nonneg_left hlip hmL.le
      simpa [← mul_assoc,ne_of_gt hmL] using hh
    have he : ga-gb = ((ga-(μ:ℝ) • a)-(gb-(μ:ℝ) • b))+(μ:ℝ) • (a-b) := by module
    have hn := norm_add_le ((ga-(μ:ℝ) • a)-(gb-(μ:ℝ) • b)) ((μ:ℝ) • (a-b))
    rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg μ.coe_nonneg] at hn
    have hfull : ‖ga-gb‖ ≤ L*‖a-b‖ := by nlinarith
    simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hLp.le]
    have hh := mul_le_mul_of_nonneg_left hfull (inv_nonneg.mpr hLp.le)
    simpa [← mul_assoc,ne_of_gt hLp] using hh
  · intro i
    refine ⟨?_,(shift_subgradient f μ μ.coe_nonneg hshift (x i) (g i)).mpr ?_⟩
    · dsimp [f];rw [(hi i).1];ring
    · simpa only [f,add_sub_cancel_right] using (hi i).2
end ConvexInterpolation
namespace ConvexInterpolation
lemma full_sufficiency {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (L : ENNReal) (hμL : (μ : ENNReal) < L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ)
    (hdata : ∀ i j, InterpIneq μ L x g fv i j) : Interpolable μ L x g fv := by
  by_cases htop : L=⊤
  · subst L
    exact (strong_interpolation μ x g fv).mpr hdata
  · have hlt : (μ:ℝ)<L.toReal := by
      simpa using (ENNReal.toReal_lt_toReal (ENNReal.coe_ne_top) htop).mpr hμL
    have he := ENNReal.ofReal_toReal htop
    rw [← he] at hdata ⊢
    exact finite_strong_sufficiency μ L.toReal hlt x g fv hdata
end ConvexInterpolation

set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped Topology
namespace ConvexInterpolation
open ShorNonsmooth.AlmostDiff
lemma subgradient_exists {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ g, IsSubgradient f x g := by
  have hc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  let epi : Set (EuclideanSpace ℝ (Fin d) × ℝ) := {p | f p.1 < p.2}
  have hepi : Convex ℝ epi := by simpa [epi] using hf.convex_strict_epigraph
  have hopen : IsOpen epi := isOpen_lt (hc.comp continuous_fst) continuous_snd
  obtain ⟨F,hF⟩ := geometric_hahn_banach_point_open hepi hopen
    (show (x,f x) ∉ epi by simp [epi])
  let c : ℝ := F (0,1)
  let ell : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ _ ℝ)
  have hsplit (z : EuclideanSpace ℝ (Fin d)) (t : ℝ) : F (z,t) = ell z+t*c := by
    have he : (z,t) = (z,0)+t • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  have hcpos : 0 < c := by
    have hh := hF (x,f x+1) (by dsimp [epi];linarith)
    rw [hsplit,hsplit] at hh
    nlinarith
  have hbound (z : EuclideanSpace ℝ (Fin d)) : ell x+c*f x ≤ ell z+c*f z := by
    by_contra hh
    have hh' := lt_of_not_ge hh
    let ε := (ell x+c*f x-(ell z+c*f z))/(2*c)
    have hε : 0 < ε := div_pos (sub_pos.mpr hh') (by positivity)
    have hp := hF (z,f z+ε) (by dsimp [epi];linarith)
    rw [hsplit,hsplit] at hp
    have he : 2*c*ε=ell x+c*f x-(ell z+c*f z) := by dsimp [ε];field_simp
    nlinarith
  let g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ((-c⁻¹) • ell)
  refine ⟨g,?_⟩
  intro z
  have hg : inner ℝ g (z-x) = -c⁻¹*(ell z-ell x) := by
    dsimp only [g]
    rw [InnerProductSpace.toDual_symm_apply]
    simp only [smul_apply,smul_eq_mul,map_sub]
    ring
  rw [hg]
  apply (mul_le_mul_iff_of_pos_left hcpos).mp
  have hh := hbound z
  have hne := ne_of_gt hcpos
  field_simp
  nlinarith
lemma smooth_hasFDeriv {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (L : ℝ)
    (hlip : ∀ x y gx gy, IsSubgradient f x gx → IsSubgradient f y gy → ‖gx-gy‖ ≤ L*‖x-y‖)
    {x gx : EuclideanSpace ℝ (Fin d)} (hgx : IsSubgradient f x gx) :
    HasFDerivAt f (InnerProductSpace.toDual ℝ _ gx) x := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  have hbound : (fun v => f (x+v)-f x-(InnerProductSpace.toDual ℝ _ gx) v)
      =O[𝓝 0] (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖^2) := by
    apply Asymptotics.IsBigO.of_bound L
    apply Filter.Eventually.of_forall
    intro v
    obtain ⟨gz,hgz⟩ := subgradient_exists f hf (x+v)
    have hl := hgx (x+v)
    have hu := hgz x
    have hb := hlip (x+v) x gz gx hgz hgx
    have hc := real_inner_le_norm (gz-gx) v
    simp only [add_sub_cancel_left] at hl hb
    have he : x-(x+v) = -v := by module
    rw [he,inner_neg_right] at hu
    simp only [inner_sub_left] at hc
    have hrem : 0 ≤ f (x+v)-f x-inner ℝ gx v := by linarith
    simp only [InnerProductSpace.toDual_apply_apply,Real.norm_eq_abs,abs_of_nonneg hrem,
      abs_of_nonneg (sq_nonneg ‖v‖)]
    nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg v)]
  exact hbound.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1<2))
end ConvexInterpolation

namespace ConvexInterpolation
open ShorNonsmooth.AlmostDiff
lemma quadratic_upper {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (L : ℝ)
    (hlip : ∀ x y gx gy, IsSubgradient f x gx → IsSubgradient f y gy → ‖gx-gy‖ ≤ L*‖x-y‖)
    {x gx : EuclideanSpace ℝ (Fin d)} (hgx : IsSubgradient f x gx)
    (z : EuclideanSpace ℝ (Fin d)) : f z ≤ f x+inner ℝ gx (z-x)+L/2*‖z-x‖^2 := by
  choose G hG using (fun z => subgradient_exists f hf z)
  let v := z-x
  let φ := fun t : ℝ => f (x+t • v)-f x-t*inner ℝ gx v-(L/2*‖v‖^2)*t^2
  let D := fun t : ℝ => inner ℝ (G (x+t • v)) v-inner ℝ gx v-L*‖v‖^2*t
  have hd (t : ℝ) : HasDerivAt φ (D t) t := by
    have hline : HasDerivAt (fun s : ℝ => x+s • v) v t := by
      convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1 <;>
        first | rfl | simp only [Pi.add_apply,zero_add,one_smul]
    have hh := (smooth_hasFDeriv f hf L hlip (hG (x+t • v))).comp_hasDerivAt t hline
    convert ((hh.sub_const (f x)).sub ((hasDerivAt_id t).mul_const (inner ℝ gx v))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L/2*‖v‖^2)) using 1 <;>
      first | rfl | (norm_num [D,InnerProductSpace.toDual_apply_apply]; ring)
  have hcont : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) hcont.continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hb := hlip (x+t • v) x (G (x+t • v)) gx (hG _) hgx
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht.1] at hb
    have hi := real_inner_le_norm (G (x+t • v)-gx) v
    simp only [inner_sub_left] at hi
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg v)]
  have hh := hanti (show (0:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num) (by norm_num)
  have he : x+(z-x)=z := by module
  simp [φ,v,he] at hh
  linarith
end ConvexInterpolation

namespace ConvexInterpolation
open ShorNonsmooth.AlmostDiff TaylorHG.PEP
lemma pair_of_upper {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (M : ℝ) (hM : 0<M)
    (x y gx gy : EuclideanSpace ℝ (Fin d)) (hy : IsSubgradient f y gy)
    (hu : ∀ z, f z ≤ f x+inner ℝ gx (z-x)+M/2*‖z-x‖^2) :
    (1/(2*M))*‖gx-gy‖^2 ≤ f x-f y-inner ℝ gy (x-y) := by
  let q : ℝ := 1/M
  let v := gx-gy
  let z := x-q • v
  have hz : z-x = -q • v := by dsimp [z];module
  have hzy : z-y = (x-y)-q • v := by dsimp [z];module
  have hlo := hy z
  have hup := hu z
  rw [hz,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,neg_sq] at hup
  rw [hzy] at hlo
  have hi : inner ℝ gx (-q • v)-inner ℝ gy ((x-y)-q • v) =
      -inner ℝ gy (x-y)-q*‖v‖^2 := by
    have hv := real_inner_self_eq_norm_sq v
    change inner ℝ (gx-gy) v=‖v‖^2 at hv
    simp only [inner_sub_left] at hv
    have hvq := congrArg (fun a : ℝ => q*a) hv
    simp only [inner_sub_right,inner_smul_right]
    nlinarith
  have hq : q-M/2*q^2=1/(2*M) := by dsimp [q];field_simp;ring
  have hw := congrArg (fun a : ℝ => a*‖v‖^2) hq
  change (1/(2*M))*‖v‖^2 ≤ _
  nlinarith
lemma shifted_upper {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (m L : ℝ)
    (x gx : EuclideanSpace ℝ (Fin d))
    (hu : ∀ z, f z ≤ f x+inner ℝ gx (z-x)+L/2*‖z-x‖^2) :
    ∀ z, f z-m/2*‖z‖^2 ≤ f x-m/2*‖x‖^2+
      inner ℝ (gx-m • x) (z-x)+(L-m)/2*‖z-x‖^2 := by
  intro z
  have hh := hu z
  have hn := norm_sub_sq_real z x
  rw [real_inner_comm] at hn
  have hw := congrArg (fun a : ℝ => m/2*a) hn
  simp only [inner_sub_right] at hh
  simp only [inner_sub_left,inner_smul_left,inner_sub_right,real_inner_self_eq_norm_sq,
    starRingEnd_apply,star_trivial]
  nlinarith
lemma unshift_data {d : ℕ} {ι : Type*} (μ : NNReal) (L : ℝ) (hL : (μ:ℝ)<L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) (i j : ι)
    (hh : (1/(2*(L-μ)))*‖(g i-(μ:ℝ) • x i)-(g j-(μ:ℝ) • x j)‖^2 ≤
      (fv i-(μ:ℝ)/2*‖x i‖^2)-(fv j-(μ:ℝ)/2*‖x j‖^2)-
        inner ℝ (g j-(μ:ℝ) • x j) (x i-x j)) :
    InterpIneq μ (ENNReal.ofReal L) x g fv i j := by
  have hLp : 0<L := lt_of_le_of_lt μ.coe_nonneg hL
  have hdiff : L-(μ:ℝ)≠0 := ne_of_gt (sub_pos.mpr hL)
  have hd : 0<1-(μ:ℝ)*L⁻¹ := by
    rw [← div_eq_mul_inv]
    exact sub_pos.mpr ((div_lt_one hLp).mpr hL)
  have hh' := mul_le_mul_of_nonneg_left hh (show 0≤2*(L-μ) by positivity)
  have he : (g i-(μ:ℝ) • x i)-(g j-(μ:ℝ) • x j)=(g i-g j)-(μ:ℝ) • (x i-x j) := by module
  rw [he,norm_sub_sq_real,inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] at hh'
  field_simp [hdiff] at hh'
  simp only [InterpIneq,ENNReal.toReal_inv,ENNReal.toReal_ofReal hLp.le]
  apply (mul_le_mul_iff_of_pos_left (mul_pos (by norm_num : (0:ℝ)<2) hd)).mp
  field_simp [ne_of_gt hLp,ne_of_gt hd,hdiff]
  simp only [mul_div_cancel_left₀ _ hdiff] at hh' ⊢
  have hn := norm_sub_sq_real (x i) (x j)
  rw [← real_inner_comm (x i) (x j)] at hn
  have hw := congrArg (fun a : ℝ => (μ:ℝ)*(L-μ)*a) hn
  simp only [inner_sub_left,inner_smul_left,inner_sub_right,real_inner_self_eq_norm_sq,
    starRingEnd_apply,star_trivial] at *
  nlinarith
lemma finite_necessity {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (L : ℝ) (hL : (μ:ℝ)<L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ)
    (hf : Interpolable μ (ENNReal.ofReal L) x g fv) :
    ∀ i j, InterpIneq μ (ENNReal.ofReal L) x g fv i j := by
  obtain ⟨f,hF,hi⟩ := hf
  have hLp : 0<L := lt_of_le_of_lt μ.coe_nonneg hL
  have hlip : ∀ a b ga gb,IsSubgradient f a ga → IsSubgradient f b gb → ‖ga-gb‖≤L*‖a-b‖ := by
    intro a b ga gb ha hb
    have hh := hF.2.1 a b ga gb ha hb
    simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hLp.le] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hLp.le
    simpa [← mul_assoc,ne_of_gt hLp] using hh'
  intro i j
  apply unshift_data μ L hL x g fv i j
  have hgy := (shift_subgradient f μ μ.coe_nonneg hF.2.2 (x j) (g j)).mp (hi j).2
  have hu := shifted_upper f μ L (x i) (g i) (quadratic_upper f hF.1 L hlip (hi i).2)
  have hh := pair_of_upper (fun z => f z-(μ:ℝ)/2*‖z‖^2) (L-μ) (sub_pos.mpr hL)
    (x i) (x j) (g i-(μ:ℝ) • x i) (g j-(μ:ℝ) • x j) hgy hu
  simpa only [(hi i).1,(hi j).1] using hh
end ConvexInterpolation

theorem solution {d : ℕ} {ι : Type*} [Fintype ι]
    (μ : NNReal) (L : ENNReal) (hμL : (μ : ENNReal) < L)
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable μ L x g fv ↔ ∀ i j, InterpIneq μ L x g fv i j := by
  constructor
  · intro hf
    by_cases htop : L=⊤
    · subst L
      exact (ConvexInterpolation.strong_interpolation μ x g fv).mp hf
    · have hlt : (μ:ℝ)<L.toReal := by
        simpa using (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top htop).mpr hμL
      have he := ENNReal.ofReal_toReal htop
      rw [← he] at hf ⊢
      exact ConvexInterpolation.finite_necessity μ L.toReal hlt x g fv hf
  · exact ConvexInterpolation.full_sufficiency μ L hμL x g fv

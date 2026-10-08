-- Prove2me | solution 1 for PenaltyLag.Exact.kt_vector_iff
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:31:46.481906+00:00
-- url     : https://prove2.me/submissions/bfcf5bcb-fc0b-4894-a711-f59848772074

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact
open PenaltyLag.Asymptotic

noncomputable def penalty {m : ℕ} (r : ℝ) (y : Mult m) (u : Fin m → ℝ) : ℝ :=
  (1/(4*r)) * ∑ i, ((max 0 (y i+2*r*u i))^2 - (y i)^2)

theorem penalty_mono {m : ℕ} {r : ℝ} (hr : 0 < r) (y : Mult m)
    {u v : Fin m → ℝ} (huv : ∀ i, u i ≤ v i) : penalty r y u ≤ penalty r y v := by
  unfold penalty
  gcongr with i
  exact huv i

theorem penalty_convex {m : ℕ} {r : ℝ} (hr : 0 < r) (y : Mult m) :
    ConvexOn ℝ Set.univ (penalty r y) := by
  have hc (i : Fin m) : ConvexOn ℝ (Set.univ : Set (Fin m → ℝ))
      (fun u => (max 0 (y i+2*r*u i))^2 - (y i)^2) := by
    have ha : ConvexOn ℝ (Set.univ : Set (Fin m → ℝ)) (fun u => y i+2*r*u i) := by
      refine ⟨convex_univ, ?_⟩
      intro u _ v _ a b ha hb hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have he : y i+2*r*(a*u i+b*v i) = a*(y i+2*r*u i)+b*(y i+2*r*v i) := by
        linear_combination -(y i)*hab
      exact he.le
    have hh := ((convexOn_const 0 convex_univ).sup ha).pow (fun u _ => le_max_left _ _) 2
    have ht := hh.add_const (-(y i)^2)
    refine ⟨convex_univ, ?_⟩
    intro u hu v hv a b ha hb hab
    simpa only [Pi.add_apply, Pi.sup_apply, Pi.pow_apply, sub_eq_add_neg] using ht.2 hu hv ha hb hab
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (hc i).2 (Set.mem_univ u) (Set.mem_univ v) ha hb hab)
  have ht := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1/(4*r) by positivity)
  simpa [penalty, Finset.sum_add_distrib, ← Finset.mul_sum, smul_eq_mul, mul_add, mul_left_comm] using ht

theorem penalty_continuous {m : ℕ} (r : ℝ) (y : Mult m) : Continuous (penalty r y) := by
  unfold penalty
  fun_prop

theorem penalty_zero {m : ℕ} {r : ℝ} (hr : 0 < r) (y : Mult m) :
    penalty r y 0 ≤ 0 := by
  unfold penalty
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply Finset.sum_nonpos; intro i _
  simp only [Pi.zero_apply, mul_zero, add_zero]
  by_cases hy : 0 ≤ y i
  · rw [max_eq_right hy]; simp
  · rw [max_eq_left (le_of_not_ge hy)]; nlinarith [sq_nonneg (y i)]

theorem functional_coordinates {m : ℕ}
    (l : StrongDual ℝ ((Fin m → ℝ) × ℝ)) (u : Fin m → ℝ) (t : ℝ) :
    l (u,t) = (∑ i, l (Pi.single i 1,0) * u i) + l (0,1)*t := by
  have he : (u,t) = (∑ i : Fin m, u i • (Pi.single i 1, (0:ℝ))) + t • (0,1) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply, eq_comm, smul_eq_mul]
    · simp [Prod.snd_sum]
  rw [he, map_add, map_sum]
  simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_comm]

theorem augmented_lower_bound_dual {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (y : Mult m) (A : ℝ)
    (hA : (A : EReal) < gr X f₀ f r y) : (A : EReal) ≤ dualValue X f₀ f := by
  classical
  let C : Set ((Fin m → ℝ) × ℝ) :=
    {p | ∃ x ∈ X, (∀ i, f i x ≤ p.1 i) ∧ f₀ x ≤ p.2}
  let D : Set ((Fin m → ℝ) × ℝ) := {p | p.2 + penalty r y p.1 < A}
  have hC : Convex ℝ C := by
    rintro p ⟨x,hx,hxf,hx₀⟩ q ⟨z,hz,hzf,hz₀⟩ a b ha hb hab
    refine ⟨a • x + b • z, hX hx hz ha hb hab, ?_, ?_⟩
    · intro i
      have hh := (hf i).2 hx hz ha hb hab
      change f i (a • x+b • z) ≤ a*p.1 i+b*q.1 i
      simp only [smul_eq_mul] at hh
      exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (hxf i) ha)
        (mul_le_mul_of_nonneg_left (hzf i) hb))
    · have hh := hf₀.2 hx hz ha hb hab
      change f₀ (a • x+b • z) ≤ a*p.2+b*q.2
      simp only [smul_eq_mul] at hh
      exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hx₀ ha)
        (mul_le_mul_of_nonneg_left hz₀ hb))
  have hD : Convex ℝ D := by
    intro p hp q hq a b ha hb hab
    have hh := (penalty_convex hr y).2 (Set.mem_univ p.1) (Set.mem_univ q.1) ha hb hab
    change a*p.2+b*q.2 + penalty r y (a • p.1+b • q.1) < A
    change p.2+penalty r y p.1 < A at hp
    change q.2+penalty r y q.1 < A at hq
    simp only [smul_eq_mul] at hh
    by_cases hb0 : b = 0
    · subst b; have ha1 : a = 1 := by linarith
      simp [ha1] at hh ⊢; linarith
    · have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have ht := add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left hp.le ha) (mul_lt_mul_of_pos_left hq hb')
      nlinarith [congrArg (fun c : ℝ => c*A) hab]
  have hDopen : IsOpen D := by
    exact isOpen_lt (continuous_snd.add ((penalty_continuous r y).comp continuous_fst)) continuous_const
  have hdis : Disjoint D C := by
    apply Set.disjoint_left.mpr
    rintro p hp ⟨x,hx,hxf,hx₀⟩
    have hh : gr X f₀ f r y ≤ (Lr f₀ f r x y : EReal) :=
      iInf_le_of_le x (iInf_le_of_le hx le_rfl)
    have hb : Lr f₀ f r x y ≤ p.2+penalty r y p.1 := by
      exact add_le_add hx₀ (penalty_mono hr y hxf)
    have ht : (Lr f₀ f r x y : EReal) < A := by exact_mod_cast hb.trans_lt hp
    exact (hA.trans_le hh).not_ge ht.le
  obtain ⟨l,v,hlD,hlC⟩ := geometric_hahn_banach_open hD hDopen hC hdis
  let μ := l (0,1)
  let ell := fun i => l (Pi.single i 1,0)
  obtain ⟨x₀,hx₀⟩ := hXne
  let u₀ := fun i => f i x₀
  have hc₀ : (u₀,f₀ x₀) ∈ C := ⟨x₀,hx₀,fun _ => le_rfl,le_rfl⟩
  let t := min (f₀ x₀-1) (A-penalty r y u₀-1)
  have htd : (u₀,t) ∈ D := by
    change t + penalty r y u₀ < A
    dsimp [t]; linarith [min_le_right (f₀ x₀-1) (A-penalty r y u₀-1)]
  have hμ : 0 < μ := by
    have hh := (hlD _ htd).trans_le (hlC _ hc₀)
    rw [functional_coordinates l u₀ t, functional_coordinates l u₀ (f₀ x₀)] at hh
    change (∑ i, ell i*u₀ i)+μ*t < (∑ i, ell i*u₀ i)+μ*f₀ x₀ at hh
    have ht : t < f₀ x₀ := by dsimp [t]; linarith [min_le_left (f₀ x₀-1) (A-penalty r y u₀-1)]
    by_contra hn
    have hm : μ ≤ 0 := le_of_not_gt hn
    nlinarith
  have hell (i : Fin m) : 0 ≤ ell i := by
    by_contra hn
    have hi : ell i < 0 := lt_of_not_ge hn
    let T := (l (u₀,f₀ x₀)-v+1)/(-ell i)
    have hT : 0 ≤ T := by
      dsimp [T]
      apply div_nonneg
      · linarith [hlC _ hc₀]
      · linarith
    have hc : (u₀ + T • Pi.single i 1, f₀ x₀) ∈ C := by
      refine ⟨x₀,hx₀,?_,le_rfl⟩
      intro j; change u₀ j ≤ u₀ j+T*(Pi.single i 1 : Fin m → ℝ) j
      have hh : 0 ≤ (Pi.single i 1 : Fin m → ℝ) j := by
        by_cases hji : j = i
        · subst j; simp
        · simp [Pi.single_apply, hji]
      nlinarith
    have hh := hlC _ hc
    have he : l (u₀ + T • Pi.single i 1, f₀ x₀) = l (u₀,f₀ x₀)+T*ell i := by
      have he : (u₀ + T • Pi.single i 1, f₀ x₀) = (u₀,f₀ x₀)+T • (Pi.single i 1,0) := by ext <;> simp
      rw [he,map_add]
      change l (u₀,f₀ x₀)+l (T • (Pi.single i 1,0)) = _
      rw [map_smul]; rfl
    rw [he] at hh
    have he' : T*(-ell i) = l (u₀,f₀ x₀)-v+1 := by
      dsimp [T]; exact div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hi))
    nlinarith
  have hv : μ*A ≤ v := by
    apply le_of_forall_lt
    intro B hB
    have hBA : B/μ < A := (div_lt_iff₀ hμ).mpr (by simpa [mul_comm] using hB)
    have hd : (0,B/μ) ∈ D := by
      change B/μ+penalty r y 0 < A
      linarith [penalty_zero hr y]
    have hh := hlD _ hd
    rw [functional_coordinates] at hh
    simpa [μ, mul_div_cancel₀ _ (ne_of_gt hμ)] using hh
  let w : Mult m := WithLp.toLp 2 (fun i => ell i/μ)
  apply le_trans (show (A : EReal) ≤ g0 X f₀ f w from ?_) (le_iSup _ w)
  apply le_iInf; intro x
  apply le_iInf; intro hx
  have hw : ∀ i, 0 ≤ w i := by intro i; exact div_nonneg (hell i) hμ.le
  simp only [L0, if_pos hw]
  have hh := hlC (fun i => f i x, f₀ x) ⟨x,hx,fun _ => le_rfl,le_rfl⟩
  rw [functional_coordinates] at hh
  have ht : A ≤ f₀ x+∑ i, w i*f i x := by
    change A ≤ f₀ x+∑ i, (ell i/μ)*f i x
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    apply (mul_le_mul_iff_right₀ hμ).mp
    have he : μ*(f₀ x+(∑ i, ell i*f i x)/μ) = μ*f₀ x+∑ i, ell i*f i x := by
      field_simp
    rw [he]
    dsimp [ell, μ] at hv ⊢
    linarith
  exact_mod_cast ht

theorem scalar_lower {r c y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) :
    4*r*(y*c) ≤ (max 0 (y+2*r*c))^2 - y^2 := by
  by_cases h : y+2*r*c ≤ 0
  · rw [max_eq_left h]
    have hh := mul_nonpos_of_nonneg_of_nonpos hy h
    nlinarith [sq_nonneg y]
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith [sq_nonneg (r*c)]

theorem ordinary_le_augmented {E : Type*} {m : ℕ} (f₀ : E → ℝ)
    (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r) (x : E) (y : Mult m) :
    L0 f₀ f x y ≤ (Lr f₀ f r x y : EReal) := by
  by_cases hy : ∀ i, 0 ≤ y i
  · simp only [L0, if_pos hy]
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => scalar_lower (c := f i x) hr (hy i))
    rw [← Finset.mul_sum] at hs
    have hp : 0 < 4*r := by positivity
    have hh : (∑ i, y i * f i x) ≤
        (1/(4*r)) * ∑ i, ((max 0 (y i+2*r*f i x))^2 - (y i)^2) := by
      rw [one_div_mul_eq_div]
      exact (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hs)
    exact_mod_cast (show f₀ x + (∑ i, y i * f i x) ≤ Lr f₀ f r x y from
      by simpa [Lr, theta] using add_le_add_left hh (f₀ x))
  · simp [L0, hy]

theorem ordinary_dual_le_augmented {E : Type*} {m : ℕ} (X : Set E)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r) :
    dualValue X f₀ f ≤ ⨆ y, gr X f₀ f r y := by
  apply iSup_le
  intro y
  apply le_trans (show g0 X f₀ f y ≤ gr X f₀ f r y from ?_) (le_iSup _ y)
  apply iInf_mono; intro x
  apply iInf_mono; intro _
  exact ordinary_le_augmented f₀ f hr x y

theorem augmented_weak_duality {E : Type*} {m : ℕ} (X : Set E)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r) (y : Mult m) :
    gr X f₀ f r y ≤ primalValue X f₀ f := by
  apply le_iInf; intro x
  apply le_iInf; intro hx
  apply le_iInf; intro hfx
  apply le_trans (iInf_le_of_le x (iInf_le_of_le hx le_rfl))
  have hs : (∑ i, ((max 0 (y i+2*r*f i x))^2 - (y i)^2)) ≤ 0 := by
    apply Finset.sum_nonpos; intro i _
    by_cases h : y i+2*r*f i x ≤ 0
    · rw [max_eq_left h]; nlinarith [sq_nonneg (y i)]
    · rw [max_eq_right (le_of_not_ge h)]
      have hrc : r*f i x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le (hfx i)
      nlinarith
  have hh := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1/(4*r) by positivity) hs
  exact_mod_cast (show Lr f₀ f r x y ≤ f₀ x from
    by simpa [Lr, theta] using add_le_add_left hh (f₀ x))

theorem kt_from_value_equality {E : Type*} {m : ℕ} (X : Set E)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (hvalue : (⨆ y, gr X f₀ f r y) = dualValue X f₀ f) (ybar : Mult m) :
    IsKTVector X f₀ f r ybar ↔ IsDualOptimal X f₀ f r ybar ∧ IsNormal X f₀ f := by
  have hw : (⨆ y, gr X f₀ f r y) ≤ primalValue X f₀ f :=
    iSup_le (augmented_weak_duality X f₀ f hr)
  constructor
  · intro hk
    have he : (⨆ y, gr X f₀ f r y) = primalValue X f₀ f := by
      apply le_antisymm hw
      rw [← hk.2]; exact le_iSup _ ybar
    exact ⟨⟨ne_of_gt hk.1, hk.2.trans he.symm⟩, hvalue.symm.trans he⟩
  · rintro ⟨hd, hn⟩
    exact ⟨bot_lt_iff_ne_bot.mpr hd.1, hd.2.trans (hvalue.trans hn)⟩

theorem dual_value_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) :
    (⨆ y, gr X f₀ f r y) = dualValue X f₀ f := by
  apply le_antisymm
  · apply iSup_le
    intro y
    by_contra hn
    obtain ⟨A, hlow, hhigh⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    have hh := augmented_lower_bound_dual X hX hXne f₀ f hf₀ hf r hr y A hhigh
    exact hlow.not_ge hh
  · exact ordinary_dual_le_augmented X f₀ f hr

end PenaltyLag.Exact
open PenaltyLag.Exact

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : PenaltyLag.Asymptotic.Mult m) :
    IsKTVector X f₀ f r ybar ↔ (IsDualOptimal X f₀ f r ybar ∧ IsNormal X f₀ f) :=
  kt_from_value_equality X f₀ f hr (dual_value_eq X hX hXne f₀ f hf₀ hf r hr) ybar
#print axioms solution

-- Prove2me | solution 1 for ShorNonsmooth.Decomposition.exists_kuhnTucker_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T20:05:47.475545+00:00
-- url     : https://prove2.me/submissions/9a6f2725-a736-43d2-8a93-06b848627c3f

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

-- Shared checked proof: ValueFnUpper

namespace ShorNonsmooth.Decomposition
open Set
open scoped Topology RealInnerProductSpace
noncomputable section

lemma vf_strict_combo {x y u v a b : ℝ} (hx : x < y) (hu : u < v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) : a*x+b*u < a*y+b*v := by
  by_cases hz : a=0
  · subst a
    have he : b=1 := by linarith
    simpa [he] using hu
  · have hp : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx hp)
      (mul_le_mul_of_nonneg_left hu.le hb)

def vf_upper {E : Type*} {n : ℕ} (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ) :
    Set ((Fin n → ℝ) × ℝ) :=
  {p | ∃ x, (∀ i, g i x < p.1 i) ∧ F x-v < p.2}

lemma vf_upper_open {E : Type*} {n : ℕ} (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ) :
    IsOpen (vf_upper F g v) := by
  have he : vf_upper F g v=⋃ x, (⋂ i : Fin n, {p : (Fin n → ℝ) × ℝ | g i x < p.1 i}) ∩
      {p : (Fin n → ℝ) × ℝ | F x-v < p.2} := by
    ext p; simp [vf_upper]
  rw [he]
  apply isOpen_iUnion
  intro x
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (by fun_prop)
  · exact isOpen_lt continuous_const continuous_snd

lemma vf_upper_convex {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ)
    (hF : ConvexOn ℝ univ F) (hg : ∀ i, ConvexOn ℝ univ (g i)) :
    Convex ℝ (vf_upper F g v) := by
  rintro p ⟨x,hx,hFx⟩ q ⟨y,hy,hFy⟩ a b ha hb hab
  refine ⟨a • x+b • y,fun i => ?_,?_⟩
  · have h := (hg i).2 (mem_univ x) (mem_univ y) ha hb hab
    have hs := vf_strict_combo (hx i) (hy i) ha hb hab
    change g i (a • x+b • y) < a*p.1 i+b*q.1 i
    simpa only [smul_eq_mul] using h.trans_lt hs
  · have h := hF.2 (mem_univ x) (mem_univ y) ha hb hab
    have hs := vf_strict_combo hFx hFy ha hb hab
    change F (a • x+b • y)-v < a*p.2+b*q.2
    simp only [smul_eq_mul] at h
    have he := congrArg (fun t : ℝ => t*v) hab
    simp only [add_mul,one_mul] at he
    nlinarith

lemma vf_upper_add {E : Type*} {n : ℕ} (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ)
    {p d : (Fin n → ℝ) × ℝ} (hp : p ∈ vf_upper F g v)
    (hd : ∀ i, 0 ≤ d.1 i) (ht : 0 ≤ d.2) : p+d ∈ vf_upper F g v := by
  obtain ⟨x,hx,hFx⟩ := hp
  exact ⟨x,fun i => (hx i).trans_le (le_add_of_nonneg_right (hd i)),
    hFx.trans_le (le_add_of_nonneg_right ht)⟩

lemma vf_split {n : ℕ} (L : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) (t : ℝ) :
    L (v,t)=(∑ i, L (Pi.single i (1:ℝ),0)*v i)+L (0,1)*t := by
  classical
  have hv : (v,(0:ℝ)) = ∑ i : Fin n, v i • (Pi.single i (1:ℝ),(0:ℝ)) := by
    simp only [Prod.smul_mk,smul_zero,← prod_mk_sum,Finset.sum_const_zero]
    exact congrArg (fun w : Fin n → ℝ => (w,(0:ℝ))) (pi_eq_sum_univ' v)
  have he : (v,t)=(v,0)+t • (0,1) := by ext <;> simp
  rw [he,map_add,map_smul,hv,map_sum]
  simp only [map_smul,smul_eq_mul,mul_comm]

lemma vf_slope_nonneg (q a : ℝ) (h : ∀ t : ℝ, 0 ≤ t → 0 < q+t*a) : 0 ≤ a := by
  by_contra hn
  have ha : a<0 := lt_of_not_ge hn
  have hq : 0<q := by simpa using h 0 (by norm_num)
  let t := (q+1)/(-a)
  have ht : 0 ≤ t := div_nonneg (by linarith) (le_of_lt (neg_pos.mpr ha))
  have he : t*a= -(q+1) := by dsimp [t]; field_simp [ne_of_lt ha] <;> ring
  have hbad := h t ht
  rw [he] at hbad
  linarith

lemma vf_coeff_nonneg {E : Type*} [Zero E] {n : ℕ}
    (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ)
    (L : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ)
    (hL : ∀ p ∈ vf_upper F g v, 0 < L p) :
    (∀ i, 0 ≤ L (Pi.single i (1:ℝ),0)) ∧ 0 ≤ L (0,1) := by
  classical
  let p : (Fin n → ℝ) × ℝ := (fun i => g i 0+1,F 0-v+1)
  have hp : p ∈ vf_upper F g v := ⟨0,fun i => by dsimp [p]; linarith,by dsimp [p]; linarith⟩
  constructor
  · intro i
    apply vf_slope_nonneg (L p)
    intro t ht
    have hmem : p+t • (Pi.single i (1:ℝ),0) ∈ vf_upper F g v := by
      apply vf_upper_add F g v hp
      · intro j
        change 0 ≤ t*(Pi.single (M := fun _ => ℝ) i (1:ℝ) j)
        have hs : 0 ≤ Pi.single (M := fun _ => ℝ) i (1:ℝ) j := by
          by_cases hj : j=i <;> simp [hj]
        exact mul_nonneg ht hs
      · simp
    simpa only [map_add,map_smul,smul_eq_mul] using hL _ hmem
  · apply vf_slope_nonneg (L p)
    intro t ht
    have hmem : p+t • (0,1) ∈ vf_upper F g v :=
      vf_upper_add F g v hp (fun _ => by simp) (by simpa using ht)
    simpa only [map_add,map_smul,smul_eq_mul] using hL _ hmem

lemma vf_upper_bound {E : Type*} {n : ℕ}
    (F : E → ℝ) (g : Fin n → E → ℝ) (v : ℝ)
    (L : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ)
    (hL : ∀ p ∈ vf_upper F g v, 0 < L p)
    (hu : ∀ i, 0 ≤ L (Pi.single i (1:ℝ),0)) (ha : 0 < L (0,1)) (x : E) :
    0 ≤ (∑ i, L (Pi.single i (1:ℝ),0)*g i x)+L (0,1)*(F x-v) := by
  let u : Fin n → ℝ := fun i => L (Pi.single i (1:ℝ),0)
  let a : ℝ := L (0,1)
  let K : ℝ := (∑ i, u i)+a
  have hsum : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => hu i)
  have hK : 0<K := by dsimp [K,a]; linarith
  change 0 ≤ (∑ i, u i*g i x)+a*(F x-v)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/K
  have hδ : 0<δ := div_pos hε hK
  have hp : (fun i => g i x+δ,F x-v+δ) ∈ vf_upper F g v :=
    ⟨x,fun i => lt_add_of_pos_right _ hδ,lt_add_of_pos_right _ hδ⟩
  have h := hL _ hp
  rw [vf_split] at h
  change 0 < (∑ i, u i*(g i x+δ))+a*(F x-v+δ) at h
  have he : (∑ i, u i*(g i x+δ))+a*(F x-v+δ)=
      (∑ i, u i*g i x)+a*(F x-v)+ε := by
    have hk : δ*K=ε := by dsimp [δ]; field_simp [ne_of_gt hK]
    dsimp [K] at hk
    rw [mul_add,Finset.mul_sum] at hk
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
    have hcomm : (∑ i, u i*δ)=∑ i, δ*u i := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hcomm]
    nlinarith
  rw [he] at h
  exact h.le

lemma vf_partial_convex {l m : ℕ}
    (F : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : JointlyConvex F) (x : EuclideanSpace ℝ (Fin l)) :
    ConvexOn ℝ univ (F x) := by
  refine ⟨convex_univ,?_⟩
  intro y hy z hz a b ha hb hab
  have h := hF.2 (mem_univ (x,y)) (mem_univ (x,z)) ha hb hab
  have he : a • x+b • x=x := by rw [← add_smul,hab,one_smul]
  simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,he] using h

end
end ShorNonsmooth.Decomposition

-- Shared checked proof: ValueFnMultiplier

namespace ShorNonsmooth.Decomposition
open Set
open scoped Topology RealInnerProductSpace
noncomputable section

-- Slater's theorem is proved for any real vector space, with finitely many constraints.
lemma vf_slater_multiplier {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (F : E → ℝ) (g : Fin n → E → ℝ)
    (hF : ConvexOn ℝ univ F) (hg : ∀ i, ConvexOn ℝ univ (g i))
    (xs : E) (hs : ∀ i, g i xs < 0)
    (x₀ : E) (hx : ∀ i, g i x₀ ≤ 0)
    (hopt : ∀ x, (∀ i, g i x ≤ 0) → F x₀ ≤ F x) :
    ∃ U : Fin n → ℝ, (∀ i, 0 ≤ U i) ∧ (∀ i, U i*g i x₀=0) ∧
      ∀ x, F x₀+(∑ i, U i*g i x₀) ≤ F x+(∑ i, U i*g i x) := by
  classical
  have hnot : (0 : (Fin n → ℝ) × ℝ) ∉ vf_upper F g (F x₀) := by
    rintro ⟨x,hxg,hxF⟩
    have h := hopt x (fun i => (hxg i).le)
    change F x-F x₀ < 0 at hxF
    linarith
  obtain ⟨L,hL⟩ := geometric_hahn_banach_point_open
    (vf_upper_convex F g (F x₀) hF hg) (vf_upper_open F g (F x₀)) hnot
  have hpos : ∀ p ∈ vf_upper F g (F x₀), 0<L p := by simpa using hL
  obtain ⟨hu,ha0⟩ := vf_coeff_nonneg F g (F x₀) L hpos
  let u : Fin n → ℝ := fun i => L (Pi.single i (1:ℝ),0)
  let a := L (0,1)
  have ha : 0<a := by
    have hm : (0,F xs-F x₀+1) ∈ vf_upper F g (F x₀) :=
      ⟨xs,hs,by linarith⟩
    have h := hpos _ hm
    rw [vf_split] at h
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,zero_add] at h
    by_contra hn
    have he : L (0,1)=0 := le_antisymm (le_of_not_gt hn) ha0
    rw [he,zero_mul] at h
    exact lt_irrefl _ h
  have hb : ∀ x, 0 ≤ (∑ i, u i*g i x)+a*(F x-F x₀) :=
    fun x => vf_upper_bound F g (F x₀) L hpos hu ha x
  have hterm : ∀ i, u i*g i x₀ ≤ 0 := fun i => mul_nonpos_of_nonneg_of_nonpos (hu i) (hx i)
  have hsum : (∑ i, u i*g i x₀)=0 := by
    have h1 := hb x₀
    have h2 : (∑ i, u i*g i x₀) ≤ 0 := Finset.sum_nonpos (fun i _ => hterm i)
    simp only [sub_self,mul_zero,add_zero] at h1
    exact le_antisymm h2 h1
  have hterms : ∀ i, u i*g i x₀=0 := by
    have hneg : (∑ i, -(u i*g i x₀))=0 := by rw [Finset.sum_neg_distrib,hsum,neg_zero]
    intro i
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => neg_nonneg.mpr (hterm j))).mp hneg i (Finset.mem_univ i)
    linarith
  let U : Fin n → ℝ := fun i => u i/a
  have hU : ∀ i, 0 ≤ U i := fun i => div_nonneg (hu i) ha.le
  have hcomp : ∀ i, U i*g i x₀=0 := by
    intro i
    change (u i/a)*g i x₀=0
    rw [div_mul_eq_mul_div,hterms,zero_div]
  refine ⟨U,hU,hcomp,fun x => ?_⟩
  have he : a*(∑ i, U i*g i x)=∑ i, u i*g i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [U]
    field_simp [ne_of_gt ha] <;> ring
  have hz : (∑ i, U i*g i x₀)=0 := Finset.sum_eq_zero (fun i _ => hcomp i)
  rw [hz,add_zero]
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith [hb x]

lemma vf_exists_multiplier {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (xbar : EuclideanSpace ℝ (Fin l)) (hslater : SlaterAt f xbar)
    (ybar : EuclideanSpace ℝ (Fin m)) (hybar : IsOptimalY f₀ f xbar ybar) :
    ∃ U : Fin n → ℝ, IsKuhnTuckerMultiplier f₀ f xbar ybar U := by
  obtain ⟨ys,hys⟩ := hslater
  obtain ⟨U,hU,hcomp,hmin⟩ := vf_slater_multiplier (f₀ xbar) (fun i => f i xbar)
    (vf_partial_convex f₀ hf₀ xbar) (fun i => vf_partial_convex (f i) (hf i) xbar)
    ys hys ybar hybar.1 hybar.2
  exact ⟨U,hU,hcomp,hmin⟩

end
end ShorNonsmooth.Decomposition

open ShorNonsmooth.Decomposition
open MeasureTheory Filter Topology

/-- Shor (1985), proof of Theorem 4.1, p. 95 ("By the Kuhn-Tucker theorem …"): for a fixed `xbar`,
if the constraints (4.4) satisfy the Slater condition and `ybar` is an optimal value of `y` in problem
(4.3)–(4.4), then Kuhn–Tucker multipliers `U ≥ 0` exist: complementary slackness holds at `ybar` and
`ybar` minimizes `L_U(xbar, ·)` over all `y`, i.e. `Φ(xbar) = min_y [f₀(xbar, y) + Σ U_i f_i(xbar, y)]`. -/
theorem solution {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (xbar : EuclideanSpace ℝ (Fin l)) (hslater : SlaterAt f xbar)
    (ybar : EuclideanSpace ℝ (Fin m)) (hybar : IsOptimalY f₀ f xbar ybar) :
    ∃ U : Fin n → ℝ, IsKuhnTuckerMultiplier f₀ f xbar ybar U := by
  exact vf_exists_multiplier f₀ f hf₀ hf xbar hslater ybar hybar

#print axioms solution

-- Prove2me | solution 1 for ShorNonsmooth.Decomposition.exists_subgradient_zero_y
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T20:06:07.720512+00:00
-- url     : https://prove2.me/submissions/54d93735-7d2f-495b-b3b0-8cf699c9dc9e

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

-- Shared checked proof: ValueFnZero

namespace ShorNonsmooth.Decomposition
open Set
open scoped Topology RealInnerProductSpace
noncomputable section

lemma vf_weighted_convex {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (U : Fin n → ℝ) (hU : ∀ i, 0 ≤ U i) (f : Fin n → E → ℝ)
    (hf : ∀ i, ConvexOn ℝ univ (f i)) : ConvexOn ℝ univ (fun x => ∑ i, U i*f i x) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  change (∑ i, U i*f i (a • x+b • y)) ≤ a*(∑ i, U i*f i x)+b*(∑ i, U i*f i y)
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left ((hf i).2 hx hy ha hb hab) (hU i)
  simp only [smul_eq_mul] at h
  nlinarith

lemma vf_lagrangian_convex {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (U : Fin n → ℝ) (hU : ∀ i, 0 ≤ U i) : JointlyConvex (lagrangian f₀ f U) := by
  have hF : ConvexOn ℝ univ
      (fun z : EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m) => f₀ z.1 z.2) := hf₀
  have hsum := vf_weighted_convex U hU
    (fun i (z : EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m)) => f i z.1 z.2) hf
  refine ⟨convex_univ,?_⟩
  intro z hz w hw a b ha hb hab
  have h0 := hF.2 hz hw ha hb hab
  have h1 := hsum.2 hz hw ha hb hab
  simp only [lagrangian,smul_eq_mul] at h0 h1 ⊢
  linarith

-- A partial minimum has a supporting subgradient with zero vertical component.
lemma vf_partial_support {l m : ℕ}
    (F : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : JointlyConvex F) (xbar : EuclideanSpace ℝ (Fin l))
    (ybar : EuclideanSpace ℝ (Fin m)) (hmin : ∀ y, F xbar ybar ≤ F xbar y) :
    ∃ gx : EuclideanSpace ℝ (Fin l), IsJointSubgradient F xbar ybar gx 0 := by
  let X := EuclideanSpace ℝ (Fin l)
  let Y := EuclideanSpace ℝ (Fin m)
  let G : X × Y → ℝ := fun p => F p.1 p.2
  let v := F xbar ybar
  let S : Set ((X × Y) × ℝ) := {p | G p.1 < p.2}
  let T : Set ((X × Y) × ℝ) := {p | p.1.1=xbar ∧ p.2=v}
  have hsc : Convex ℝ S := by simpa only [mem_univ,true_and] using hF.convex_strict_epigraph
  have hc : Continuous G := continuousOn_univ.mp (hF.continuousOn isOpen_univ)
  have hso : IsOpen S := isOpen_lt (hc.comp continuous_fst) continuous_snd
  have htc : Convex ℝ T := by
    intro p hp q hq a b ha hb hab
    constructor
    · change a • p.1.1+b • q.1.1=xbar
      rw [hp.1,hq.1,← add_smul,hab,one_smul]
    · change a*p.2+b*q.2=v
      rw [hp.2,hq.2,← add_mul,hab,one_mul]
  have hdisj : Disjoint S T := by
    apply disjoint_left.mpr
    intro p hp ht
    change F p.1.1 p.1.2 < p.2 at hp
    rw [ht.1,ht.2] at hp
    exact (not_lt_of_ge (hmin p.1.2)) hp
  obtain ⟨L,u,hS,hT⟩ := geometric_hahn_banach_open hsc hso htc hdisj
  let a : ℝ := L ((0,0),1)
  have hsplit : ∀ (x : X) (y : Y) (t : ℝ),
      L ((x,y),t)=L ((x,0),0)+L ((0,y),0)+t*a := by
    intro x y t
    have he : ((x,y),t)=((x,0),0)+((0,y),0)+t • ((0,0),1) := by ext <;> simp
    rw [he,map_add,map_add,map_smul]
    rfl
  have ha : a<0 := by
    have h1 := hS ((xbar,ybar),v+1) (by change F xbar ybar < v+1; dsimp [v]; linarith)
    have h2 := hT ((xbar,ybar),v) ⟨rfl,rfl⟩
    rw [hsplit xbar ybar (v+1)] at h1
    rw [hsplit xbar ybar v] at h2
    linarith
  have hb : ∀ x : X, ∀ y : Y, L ((x,y),F x y) ≤ u := by
    intro x y
    apply le_of_forall_pos_le_add
    intro ε hε
    have h := hS ((x,y),F x y+ε/(-a))
      (by change F x y < F x y+ε/(-a); exact lt_add_of_pos_right _ (div_pos hε (neg_pos.mpr ha)))
    rw [hsplit x y (F x y+ε/(-a))] at h
    rw [hsplit x y (F x y)]
    have he : a*(ε/(-a))= -ε := by field_simp [ne_of_lt ha]
    nlinarith
  have hu : u=L ((xbar,ybar),v) :=
    le_antisymm (hT ((xbar,ybar),v) ⟨rfl,rfl⟩) (hb xbar ybar)
  have hvertical : ∀ y : Y, L ((0,y),0)=0 := by
    intro y
    have hp := hT ((xbar,ybar+y),v) ⟨rfl,rfl⟩
    have hm := hT ((xbar,ybar-y),v) ⟨rfl,rfl⟩
    have heplus : ((xbar,ybar+y),v)=((xbar,ybar),v)+((0,y),0) := by
      change ((xbar,ybar+y),v)=((xbar+0,ybar+y),v+0)
      simp
    have heminus : ((xbar,ybar-y),v)=((xbar,ybar),v)-((0,y),0) := by
      change ((xbar,ybar-y),v)=((xbar-0,ybar-y),v-0)
      simp
    rw [heplus,map_add,hu] at hp
    rw [heminus,map_sub,hu] at hm
    linarith
  let lx : X →L[ℝ] ℝ := L.comp ((ContinuousLinearMap.inl ℝ (X × Y) ℝ).comp
    (ContinuousLinearMap.inl ℝ X Y))
  let gx : X := (-a⁻¹) • (InnerProductSpace.toDual ℝ X).symm lx
  have hi : ∀ x : X, a*inner ℝ gx (x-xbar)= -(L ((x,0),0)-L ((xbar,0),0)) := by
    intro x
    dsimp only [gx]
    rw [real_inner_smul_left,InnerProductSpace.toDual_symm_apply,map_sub]
    change a*((-a⁻¹)*(L ((x,0),0)-L ((xbar,0),0)))= -(L ((x,0),0)-L ((xbar,0),0))
    field_simp [ne_of_lt ha] <;> ring
  refine ⟨gx,?_⟩
  intro x y
  have h := hb x y
  rw [hu,hsplit x y (F x y),hsplit xbar ybar v,hvertical y,hvertical ybar] at h
  change inner ℝ gx (x-xbar)+inner ℝ (0:Y) (y-ybar) ≤ F x y-v
  rw [inner_zero_left,add_zero]
  apply (mul_le_mul_iff_right₀ (neg_pos.mpr ha)).mp
  nlinarith [hi x]

lemma vf_exists_zero_y {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (xbar : EuclideanSpace ℝ (Fin l)) (ybar : EuclideanSpace ℝ (Fin m))
    (U : Fin n → ℝ) (hU : IsKuhnTuckerMultiplier f₀ f xbar ybar U) :
    ∃ gx : EuclideanSpace ℝ (Fin l), IsJointSubgradient (lagrangian f₀ f U) xbar ybar gx 0 := by
  exact vf_partial_support (lagrangian f₀ f U) (vf_lagrangian_convex f₀ f hf₀ hf U hU.1)
    xbar ybar hU.2.2

end
end ShorNonsmooth.Decomposition

open ShorNonsmooth.Decomposition
open MeasureTheory Filter Topology

/-- Shor (1985), proof of Theorem 4.1, p. 95 ("this is always possible, since
`L_U(x̄, y(x̄)) = min L(x̄, y)`"): if `f₀` and all `f_i` are jointly convex and `U` are Kuhn–Tucker
multipliers at `xbar` for the optimal point `ybar` (so `ybar` minimizes `L_U(xbar, ·)`), then the Lagrange
function `L_U` has a subgradient at `(xbar, ybar)` whose projection on the `y`-space vanishes. -/
theorem solution {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (xbar : EuclideanSpace ℝ (Fin l)) (ybar : EuclideanSpace ℝ (Fin m))
    (U : Fin n → ℝ) (hU : IsKuhnTuckerMultiplier f₀ f xbar ybar U) :
    ∃ gx : EuclideanSpace ℝ (Fin l), IsJointSubgradient (lagrangian f₀ f U) xbar ybar gx 0 := by
  exact vf_exists_zero_y f₀ f hf₀ hf xbar ybar U hU

#print axioms solution

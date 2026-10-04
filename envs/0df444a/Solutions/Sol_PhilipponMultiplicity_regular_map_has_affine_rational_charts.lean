-- Prove2me | solution 1 for PhilipponMultiplicity.regular_map_has_affine_rational_charts
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T19:06:59.840124+00:00
-- url     : https://prove2.me/submissions/57b66024-b9e3-40d9-98a7-f6082a5232ee

import Theorems.Thm_PhilipponMultiplicity_exists_affine_embedding_chart_in_open
import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib

section
-- Included implementation: Solutions.PhilipponProjectiveGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩


end MultiProjectiveSpace
end PhilipponMultiplicity
end
end


section
-- Included implementation: Solutions.PhilipponHomogeneousOperations

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Included implementation: Solutions.PhilipponProjectiveContact
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring


end PhilipponMultiplicity
end
end


section
-- Included implementation: Solutions.PhilipponAdditiveSubgroups

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)


end PhilipponMultiplicity
end
end


section
-- Included implementation: Solutions.PhilipponRegularMapTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

/-- Substituting tuples homogeneous in each source block preserves
multihomogeneity, with the expected linear transformation of degrees. -/
theorem IsHomogeneous.eval₂_blocks (M N : MultiProjectiveSpace K)
    {Q : N.CoordinateRing} {D : N.FactorIndex → ℕ} (hQ : N.IsHomogeneous Q D)
    (P : N.Variable → M.CoordinateRing) (E : N.FactorIndex → M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) (E j.1)) :
    M.IsHomogeneous (eval₂ C P Q) (fun i => ∑ b, D b * E b i) := by
  classical
  rw [eval₂_eq']
  apply M.isHomogeneous_sum
  intro d hd
  have hh := M.isHomogeneous_prod Finset.univ (fun j => P j ^ d j)
    (fun j i => d j * E j.1 i) (fun j _ => (hP j).pow M (d j))
  have he : (∑ j : N.Variable, fun i => d j * E j.1 i) =
      (fun i => ∑ b, D b * E b i) := by
    funext i
    simp only [Finset.sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ y, d ⟨b, y⟩ * E b i) = D b * E b i
    rw [← Finset.sum_mul, hQ d hd b]
  rw [he] at hh
  exact hh.C_mul M _

/-- Regular maps are continuous for the actual polynomial Zariski topologies. -/
theorem IsRegularAlong.continuous
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) :
    @Continuous X N.Point (TopologicalSpace.induced e M.zariskiTopology)
      N.zariskiTopology f := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨R, D, hR, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  choose U hU hxU E P hP hlift using hf x
  let pull := eval₂ C (fun j : N.Variable => P j.1 j.2) R
  have hpull : M.IsHomogeneous pull (fun i => ∑ b, D b * E b i) :=
    hR.eval₂_blocks M N _ E (fun j => hP j.1 j.2)
  have heval (y : X) : M.eval pull (e y) =
      MvPolynomial.eval (fun j : N.Variable => M.eval (P j.1 j.2) (e y)) R := by
    dsimp only [eval, pull]
    rw [← eval_assoc]
    rfl
  have hiff (y : X) (hy : ∀ b, e y ∈ U b) :
      M.eval pull (e y) = 0 ↔ N.eval R (f y) = 0 := by
    rw [heval]
    exact N.eval_eq_zero_iff_of_lift (f y) _ (fun b => hlift b y (hy b)) R D hR
  let W : Set M.Point := (⋂ b, U b) ∩ {p | M.eval pull p ≠ 0}
  have hW : IsOpen (e ⁻¹' W) :=
    ((isOpen_iInter_of_finite hU).inter (M.isOpen_basic _ _ hpull)).preimage
      continuous_induced_dom
  have hxW : x ∈ e ⁻¹' W := ⟨Set.mem_iInter.mpr hxU, (hiff x hxU).not.mpr hx⟩
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  intro y hy
  exact (hiff y (Set.mem_iInter.mp hy.1)).not.mp hy.2


end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Included implementation: Solutions.PhilipponRegularMapComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem homogeneous_tuple_lift {ι : Type*} (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hn : (fun j => M.eval (P j) p) ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (P j)) h =
        Projectivization.mk K (fun j => M.eval (P j) p) hn := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  let b : K := ∏ i, (a i : K) ^ D i
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (a i).ne_zero)
  have heval : (fun j => MvPolynomial.eval v (P j)) = b • (fun j => M.eval (P j) p) := by
    funext j
    rw [hv', M.eval_block_scale (P j) D (hP j) (M.coordinate p) (fun i => (a i : K))]
    rfl
  have hn' : (fun j => MvPolynomial.eval v (P j)) ≠ 0 := by
    rw [heval]
    exact smul_ne_zero hb hn
  exact ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, heval.symm⟩⟩


end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Included implementation: Solutions.PhilipponAffineMapFractions

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

/-- A balanced homogeneous fraction is unchanged when each projective block
is replaced by another nonzero representative. -/
theorem eval_ratio_of_lift (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P Q : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    MvPolynomial.eval v P / MvPolynomial.eval v Q = M.eval P p / M.eval Q p := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h (p i).rep_nonzero).mp
      (he.trans (p i).mk_rep.symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K)),
    M.eval_block_scale Q D hQ (M.coordinate p) (fun i => (a i : K))]
  exact mul_div_mul_left _ _ hne

/-- Polynomial projective lifts of a source chart turn a regular map into
local polynomial projective lifts of the target. -/
theorem IsRegularAlong.local_polynomial_lift
    {X : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point}
    (hf : M.IsRegularAlong N e f) (S : Set X) {σ : Type*}
    (a : S → σ → K) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ w : S, ∀ b, ∃ h : (fun i => aeval (a w) (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval (a w) (L ⟨b, i⟩)) h = e w.val b)
    (z : S) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ U : Set S, IsOpen U ∧ z ∈ U ∧
      ∃ R : N.Variable → MvPolynomial σ K,
        ∀ w ∈ U, ∀ b, ∃ h : (fun i => aeval (a w) (R ⟨b, i⟩)) ≠ 0,
          Projectivization.mk K (fun i => aeval (a w) (R ⟨b, i⟩)) h = f w.val b := by
  classical
  letI := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  choose U hU hzU D P hP hrep using hf z.val
  let V : Set S := ⋂ b, (fun w : S => e w.val) ⁻¹' U b
  let R : N.Variable → MvPolynomial σ K := fun t => eval₂ C L (P t.1 t.2)
  refine ⟨V, isOpen_iInter_of_finite (fun b =>
    (hU b).preimage (continuous_induced_dom.comp continuous_subtype_val)),
    mem_iInter.mpr hzU, R, ?_⟩
  intro w hw b
  obtain ⟨hn, he⟩ := hrep b w.val (mem_iInter.mp hw b)
  obtain ⟨hn', he'⟩ := M.homogeneous_tuple_lift (e w.val)
    (fun v => aeval (a w) (L v)) (hL w) (P b) (D b) (hP b) hn
  have heval (i) : aeval (a w) (R ⟨b, i⟩) =
      MvPolynomial.eval (fun v => aeval (a w) (L v)) (P b i) := by
    change MvPolynomial.eval (a w) (eval₂ C L (P b i)) = _
    rw [← eval_assoc]
    rfl
  simpa only [heval] using ⟨hn', he'.trans he⟩

/-- Balanced rational functions on the target pull back to local fractions
in any source coordinates admitting polynomial projective lifts. -/
theorem IsRegularAlong.local_fraction_of_target_ratio
    {X : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point}
    (hf : M.IsRegularAlong N e f) (S : Set X) {σ : Type*}
    (a : S → σ → K) (L : M.Variable → MvPolynomial σ K)
    (hL : ∀ w : S, ∀ b, ∃ h : (fun i => aeval (a w) (L ⟨b, i⟩)) ≠ 0,
      Projectivization.mk K (fun i => aeval (a w) (L ⟨b, i⟩)) h = e w.val b)
    (P Q : N.CoordinateRing) (D : N.FactorIndex → ℕ)
    (hP : N.IsHomogeneous P D) (hQ : N.IsHomogeneous Q D)
    (hQne : ∀ w : S, N.eval Q (f w.val) ≠ 0) (z : S) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ U : Set S, IsOpen U ∧ z ∈ U ∧ ∃ A B : MvPolynomial σ K,
      ∀ w ∈ U, aeval (a w) B ≠ 0 ∧
        N.eval P (f w.val) / N.eval Q (f w.val) =
          aeval (a w) A / aeval (a w) B := by
  classical
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  obtain ⟨U, hU, hzU, R, hR⟩ := hf.local_polynomial_lift S a L hL z
  refine ⟨U, hU, hzU, eval₂ C R P, eval₂ C R Q, ?_⟩
  intro w hw
  have heval (F : N.CoordinateRing) : aeval (a w) (eval₂ C R F) =
      MvPolynomial.eval (fun v => aeval (a w) (R v)) F := by
    change MvPolynomial.eval (a w) (eval₂ C R F) = _
    rw [← eval_assoc]
    rfl
  simp only [heval]
  exact ⟨(N.eval_eq_zero_iff_of_lift _ _ (hR w hw) Q D hQ).not.mpr (hQne w),
    (N.eval_ratio_of_lift _ _ (hR w hw) P Q D hP hQ).symm⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end
end


section
-- Included implementation: Solutions.PhilipponEmbeddingChartsReduction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity
universe u

/-- A chart theorem for single embedded sets suffices for compatible rational
charts of every regular map. All map compatibility is proved here. -/
theorem rational_charts_of_embedding_charts
    (K : Type u) [Field K] [IsAlgClosed K]
    (M N : MultiProjectiveSpace K) (X Y : Type u)
    (e : X → M.Point) (j : Y → N.Point) (f : X → Y)
    (he : Function.Injective e) (hj : Function.Injective j)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (hY : @IsLocallyClosed _ N.zariskiTopology (Set.range j))
    (hf : M.IsRegularAlong N e (j ∘ f)) (x : X)
    (hcharts :
    ∀ (M : MultiProjectiveSpace K) (X : Type u) (e : X → M.Point)
    (he : Function.Injective e)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (x : X) (W : Set X)
    (hW : @IsOpen X (TopologicalSpace.induced e M.zariskiTopology) W)
    (hxW : x ∈ W),
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ S ⊆ W ∧
      ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance),
        (∃ L : M.Variable → MvPolynomial (Fin n) K,
          ∀ z : S, ∀ b, ∃ h :
            (fun i => MvPolynomial.aeval (a z).val (L ⟨b, i⟩)) ≠ 0,
            Projectivization.mk K
              (fun i => MvPolynomial.aeval (a z).val (L ⟨b, i⟩)) h = e z.val b) ∧
        (∀ i : Fin n, ∃ (D : M.FactorIndex → ℕ) (P Q : M.CoordinateRing),
          M.IsHomogeneous P D ∧ M.IsHomogeneous Q D ∧
          ∀ z : S, M.eval Q (e z.val) ≠ 0 ∧
            (a z).val i = M.eval P (e z.val) / M.eval Q (e z.val))
    ) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    letI : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
    ∃ (S : Set X) (T : Set Y), IsOpen S ∧ x ∈ S ∧ IsOpen T ∧
      ∃ hST : Set.MapsTo f S T,
      ∃ (m n : ℕ) (I : Ideal (MvPolynomial (Fin m) K))
        (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ (a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance))
        (b : @Homeomorph T (MvPolynomial.zeroLocus K I) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K I => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance)),
        ∀ (z : S) (i : Fin m), ∃ U : Set S, IsOpen U ∧ z ∈ U ∧
          ∃ P Q : MvPolynomial (Fin n) K, ∀ w ∈ U,
            MvPolynomial.aeval (a w).val Q ≠ 0 ∧
            (b ⟨f w.val, hST w.property⟩).val i =
              MvPolynomial.aeval (a w).val P / MvPolynomial.aeval (a w).val Q := by
  classical
  letI := M.zariskiTopology
  letI := N.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  letI : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
  have hfc : Continuous f := continuous_induced_rng.mpr hf.continuous
  obtain ⟨T, hT, hfxT, _, m, I, _, b, _, hcoords⟩ :=
    hcharts N Y j hj hY (f x) Set.univ isOpen_univ (Set.mem_univ _)
  obtain ⟨S, hS, hxS, hST, n, J, hJ, a, ⟨L, hL⟩, _⟩ :=
    hcharts M X e he hX x (f ⁻¹' T) (hT.preimage hfc) hfxT
  refine ⟨S, T, hS, hxS, hT, hST, m, n, I, J, hJ, a, b, ?_⟩
  intro z i
  obtain ⟨D, P, Q, hP, hQ, hratio⟩ := hcoords i
  obtain ⟨U, hU, hzU, A, B, hAB⟩ := hf.local_fraction_of_target_ratio S
    (fun w => (a w).val) L hL P Q D hP hQ
    (fun w => (hratio ⟨f w.val, hST w.property⟩).1) z
  refine ⟨U, hU, hzU, A, B, ?_⟩
  intro w hw
  exact ⟨(hAB w hw).1, (hratio ⟨f w.val, hST w.property⟩).2.trans (hAB w hw).2⟩

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K]
    (M N : MultiProjectiveSpace K) (X Y : Type u)
    (e : X → M.Point) (j : Y → N.Point) (f : X → Y)
    (he : Function.Injective e) (hj : Function.Injective j)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (hY : @IsLocallyClosed _ N.zariskiTopology (Set.range j))
    (hf : M.IsRegularAlong N e (j ∘ f)) (x : X) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    letI : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
    ∃ (S : Set X) (T : Set Y), IsOpen S ∧ x ∈ S ∧ IsOpen T ∧
      ∃ hST : Set.MapsTo f S T,
      ∃ (m n : ℕ) (I : Ideal (MvPolynomial (Fin m) K))
        (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ (a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance))
        (b : @Homeomorph T (MvPolynomial.zeroLocus K I) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K I => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance)),
        ∀ (z : S) (i : Fin m), ∃ U : Set S, IsOpen U ∧ z ∈ U ∧
          ∃ P Q : MvPolynomial (Fin n) K, ∀ w ∈ U,
            MvPolynomial.aeval (a w).val Q ≠ 0 ∧
            (b ⟨f w.val, hST w.property⟩).val i =
              MvPolynomial.aeval (a w).val P / MvPolynomial.aeval (a w).val Q := by
  exact rational_charts_of_embedding_charts K M N X Y e j f he hj hX hY hf x
    (exists_affine_embedding_chart_in_open K)

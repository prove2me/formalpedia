-- Prove2me | solution 1 for WeierstrassEllipticZeta.analytic_additive_identity_component
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T03:23:17.32396+00:00
-- url     : https://prove2.me/submissions/ebe3ec01-9051-48ab-9652-11c978d73b05

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Subgroup
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Sequences
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity


-- Source: Solutions/ClosedComplexSubgroupTangents.lean

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace AddSubgroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The largest complex vector subspace contained in an additive subgroup. -/
def complexCore (K : AddSubgroup E) : Submodule ℂ E where
  carrier := {v | ∀ c : ℂ, c • v ∈ K}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw c
    simpa only [smul_add] using K.add_mem (hv c) (hw c)
  smul_mem' := by
    intro c v hv a
    simpa only [mul_smul] using hv (a * c)

theorem complexCore_le (K : AddSubgroup E) : (K.complexCore : Set E) ⊆ K := by
  intro v hv
  simpa using hv 1

/-- A differentiable curve lying in a closed additive subgroup has all complex
multiples of its tangent in the subgroup. Integer multiples of its shrinking
increments converge to each such tangent; scalar closure is proved, not assumed. -/
theorem hasDerivAt_mem_complexCore_of_eventually (K : AddSubgroup E) (hK : IsClosed (K : Set E))
    (f : ℂ → E) (f' : E) (hf : HasDerivAt f f' 0)
    (hmem : ∀ᶠ z in 𝓝 (0 : ℂ), f z ∈ K) : f' ∈ K.complexCore := by
  intro c
  have hg : HasDerivAt (fun z : ℂ => f (c * z)) (c • f') 0 := by
    have hh : HasDerivAt f f' (c * 0) := by simpa using hf
    simpa only [Function.comp_def, mul_one] using!
      hh.scomp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul c)
  have hn : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall ?_⟩
    intro n
    have h : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using one_div_ne_zero h
  have ht := hg.tendsto_slope_zero.comp hn
  apply hK.mem_of_tendsto ht
  have hseq : Tendsto (fun n : ℕ => c * (1 / ((n : ℂ) + 1))) atTop (𝓝 (0 : ℂ)) := by
    simpa using tendsto_const_nhds.mul (hn.mono_right nhdsWithin_le_nhds)
  filter_upwards [hseq.eventually hmem] with n hfn
  change (1 / ((n : ℂ) + 1))⁻¹ • (f (c * (0 + 1 / ((n : ℂ) + 1))) - f (c * 0)) ∈ K
  simp only [one_div, inv_inv, zero_add, mul_zero]
  have hh := K.nsmul_mem (K.sub_mem (by simpa only [one_div] using hfn)
    hmem.self_of_nhds) (n + 1)
  simpa only [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_add, Nat.cast_one] using hh

theorem hasDerivAt_mem_complexCore (K : AddSubgroup E) (hK : IsClosed (K : Set E))
    (f : ℂ → E) (f' : E) (hf : HasDerivAt f f' 0)
    (hmem : ∀ z : ℂ, f z ∈ K) : f' ∈ K.complexCore :=
  K.hasDerivAt_mem_complexCore_of_eventually hK f f' hf (Filter.Eventually.of_forall hmem)

end AddSubgroup
end

-- Source: Solutions/ClosedAnalyticSubgroupLocal.lean

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace AddSubgroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A real line in an entire common zero locus extends to a complex line. -/
theorem mem_complexCore_of_real_line
    (K : AddSubgroup E) (F : Set (E → ℂ))
    (hF : ∀ f ∈ F, AnalyticOnNhd ℂ f univ)
    (hzero : ∀ x, x ∈ K ↔ ∀ f ∈ F, f x = 0)
    (v : E) (hv : ∀ r : ℝ, (r : ℂ) • v ∈ K) : v ∈ K.complexCore := by
  intro c
  apply (hzero _).mpr
  intro f hf
  have ha : AnalyticOnNhd ℂ (fun z : ℂ => f (z • v)) univ := by
    intro z _
    exact (hF f hf _ trivial).comp (analyticAt_id.smul analyticAt_const)
  have hn : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall ?_⟩
    intro n
    have hh : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa using one_div_ne_zero hh
  have hz : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f (z • v) = 0 :=
    hn.frequently <| .of_forall fun n => by
      have hh := (hzero _).mp (hv (1 / ((n : ℝ) + 1))) f hf
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
        Complex.ofReal_natCast] using hh
  exact ha.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ trivial hz (mem_univ c)

/-- Normalized small subgroup elements generate a real line in a closed subgroup.
Integer multiples approximate each real scalar, with error less than one increment. -/
theorem real_line_mem_of_normalized_limit
    (K : AddSubgroup E) (hK : IsClosed (K : Set E))
    (x : ℕ → E) (hx : ∀ n, x n ∈ K) (hne : ∀ n, x n ≠ 0)
    (hsmall : Tendsto x atTop (𝓝 0)) (v : E)
    (hv : Tendsto (fun n => ((‖x n‖⁻¹ : ℝ) : ℂ) • x n) atTop (𝓝 v)) :
    ∀ r : ℝ, (r : ℂ) • v ∈ K := by
  intro r
  let a : ℕ → ℝ := fun n => (⌊r / ‖x n‖⌋ : ℤ) * ‖x n‖
  have ha : Tendsto a atTop (𝓝 r) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hsmall.norm)
    have hp : 0 < ‖x n‖ := norm_pos_iff.mpr (hne n)
    have hlow := Int.sub_floor_div_mul_nonneg r hp
    have hupp := Int.sub_floor_div_mul_lt r hp
    dsimp only [a]
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hlow]
    exact hupp.le
  have ht := (Complex.continuous_ofReal.continuousAt.tendsto.comp ha).smul hv
  have heq (n : ℕ) :
      (a n : ℂ) • (((‖x n‖⁻¹ : ℝ) : ℂ) • x n) = (⌊r / ‖x n‖⌋ : ℤ) • x n := by
    rw [smul_smul, ← Int.cast_smul_eq_zsmul ℂ]
    congr 1
    have hn : ‖x n‖ ≠ 0 := norm_ne_zero_iff.mpr (hne n)
    dsimp only [a]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hn]
  apply hK.mem_of_tendsto ht
  exact .of_forall fun n => heq n ▸ K.zsmul_mem (hx n) _

variable [FiniteDimensional ℂ E]

/-- A complement to the maximal complex subspace meets an analytic subgroup
discretely. Otherwise normalized small elements yield a nonzero core vector in
the complement. -/
theorem exists_pos_complement_isolated
    (K : AddSubgroup E) (hK : IsClosed (K : Set E)) (F : Set (E → ℂ))
    (hF : ∀ f ∈ F, AnalyticOnNhd ℂ f univ)
    (hzero : ∀ x, x ∈ K ↔ ∀ f ∈ F, f x = 0)
    (W : Submodule ℂ E) (hW : Disjoint K.complexCore W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, x ∈ W → ‖x‖ < ε → x = 0 := by
  classical
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  by_contra h
  push Not at h
  have hchoose (n : ℕ) : ∃ x : E,
      x ∈ K ∧ x ∈ W ∧ ‖x‖ < 1 / ((n : ℝ) + 1) ∧ x ≠ 0 :=
    h _ (by positivity)
  choose x hxK hxW hxnorm hxne using hchoose
  have hsmall : Tendsto x atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hxnorm n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  let y : ℕ → E := fun n => ((‖x n‖⁻¹ : ℝ) : ℂ) • x n
  have hynorm (n : ℕ) : ‖y n‖ = 1 := by
    simp only [y, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hxne n))
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    (fun n => show y n ∈ Metric.sphere (0 : E) 1 by simpa using hynorm n)
  have hcv : v ∈ K.complexCore := K.mem_complexCore_of_real_line F hF hzero v
    (K.real_line_mem_of_normalized_limit hK (x ∘ φ) (fun n => hxK (φ n))
      (fun n => hxne (φ n)) (hsmall.comp hφ.tendsto_atTop) v hlim)
  have hwv : v ∈ W := W.closed_of_finiteDimensional.mem_of_tendsto hlim
    (.of_forall fun n => W.smul_mem _ (hxW (φ n)))
  have hvzero : v = 0 := Submodule.disjoint_def.mp hW v hcv hwv
  simp [hvzero] at hv

/-- Near the identity, a finite-dimensional closed analytic additive subgroup
is exactly its maximal complex vector subspace. Discrete periods away from the
identity are allowed. -/
theorem eventually_mem_iff_complexCore
    (K : AddSubgroup E) (hK : IsClosed (K : Set E)) (F : Set (E → ℂ))
    (hF : ∀ f ∈ F, AnalyticOnNhd ℂ f univ)
    (hzero : ∀ x, x ∈ K ↔ ∀ f ∈ F, f x = 0) :
    ∀ᶠ x in 𝓝 (0 : E), x ∈ K ↔ x ∈ K.complexCore := by
  classical
  obtain ⟨W, hW⟩ := K.complexCore.exists_isCompl
  obtain ⟨ε, hε, hiso⟩ := K.exists_pos_complement_isolated hK F hF hzero W hW.disjoint
  let P : E →ₗ[ℂ] E := K.complexCore.projection W hW
  have hcont : Tendsto (fun x => x - P x) (𝓝 (0 : E)) (𝓝 0) := by
    simpa using! (continuous_id.sub P.continuous_of_finiteDimensional).tendsto (0 : E)
  have hsmall : ∀ᶠ x in 𝓝 (0 : E), ‖x - P x‖ < ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hcont.eventually (Metric.ball_mem_nhds (0 : E) hε)
  filter_upwards [hsmall] with x hx
  refine ⟨fun hmem => ?_, fun hm => K.complexCore_le hm⟩
  have hP : P x ∈ K.complexCore := (K.complexCore.projectionOnto W hW x).property
  have hsub := hiso (x - P x) (K.sub_mem hmem (K.complexCore_le hP))
    (K.complexCore.sub_projection_mem hW x) hx
  exact (sub_eq_zero.mp hsub).symm ▸ hP

/-- The identity component in the usual norm topology of a closed analytic
additive subgroup is a complex vector subspace. This does not identify analytic
connectedness with Zariski connectedness. -/
theorem connectedComponentIn_eq_complexCore
    (K : AddSubgroup E) (hK : IsClosed (K : Set E)) (F : Set (E → ℂ))
    (hF : ∀ f ∈ F, AnalyticOnNhd ℂ f univ)
    (hzero : ∀ x, x ∈ K ↔ ∀ f ∈ F, f x = 0) :
    connectedComponentIn (K : Set E) 0 = (K.complexCore : Set E) := by
  let J : AddSubgroup K := K.complexCore.toAddSubgroup.comap K.subtype
  have hnear := (continuous_subtype_val.tendsto (0 : K)).eventually
    (K.eventually_mem_iff_complexCore hK F hF hzero)
  have hopen : IsOpen (J : Set K) := J.isOpen_of_mem_nhds
    (hnear.mono fun x hx => hx.mp x.property)
  have hclosed : IsClosed (J : Set K) :=
    K.complexCore.closed_of_finiteDimensional.preimage continuous_subtype_val
  apply Subset.antisymm
  · rw [connectedComponentIn_eq_image K.zero_mem]
    rintro x ⟨y, hy, rfl⟩
    exact (show IsClopen (J : Set K) from ⟨hclosed, hopen⟩).connectedComponent_subset
      J.zero_mem hy
  · let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    have hpre : IsPreconnected (K.complexCore : Set E) :=
      (K.complexCore.restrictScalars ℝ).convex.isPreconnected
    exact hpre.subset_connectedComponentIn K.complexCore.zero_mem K.complexCore_le

end AddSubgroup

end

noncomputable section
namespace WeierstrassEllipticZeta
theorem analytic_additive_identity_component
    (K : AddSubgroup (Fin 3 → ℂ)) (F : Finset ((Fin 3 → ℂ) → ℂ))
    (hF : ∀ f ∈ F, AnalyticOnNhd ℂ f Set.univ)
    (hzero : ∀ v, v ∈ K ↔ ∀ f ∈ F, f v = 0) :
    ∃ V : Submodule ℂ (Fin 3 → ℂ),
      (V : Set (Fin 3 → ℂ)) = connectedComponentIn (K : Set (Fin 3 → ℂ)) 0 := by
  have hclosed : IsClosed (K : Set (Fin 3 → ℂ)) := by
    have heq : (K : Set (Fin 3 → ℂ)) = ⋂ f ∈ F, {v | f v = 0} := by
      ext v
      simpa using hzero v
    rw [heq]
    apply isClosed_biInter
    intro f hf
    exact isClosed_eq (continuous_iff_continuousAt.mpr
      (fun v => (hF f hf v trivial).continuousAt)) continuous_const
  exact ⟨K.complexCore, (K.connectedComponentIn_eq_complexCore hclosed
    (F : Set ((Fin 3 → ℂ) → ℂ)) hF hzero).symm⟩

end WeierstrassEllipticZeta
end
theorem solution
    (K : AddSubgroup (Fin 3 → ℂ)) (F : Finset ((Fin 3 → ℂ) → ℂ))
    (hF : ∀ f ∈ F, AnalyticOnNhd ℂ f Set.univ)
    (hzero : ∀ v, v ∈ K ↔ ∀ f ∈ F, f v = 0) :
    ∃ V : Submodule ℂ (Fin 3 → ℂ),
      (V : Set (Fin 3 → ℂ)) = connectedComponentIn (K : Set (Fin 3 → ℂ)) 0 := by
  exact WeierstrassEllipticZeta.analytic_additive_identity_component K F hF hzero
#print axioms solution

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymStability_proof_fff293b9fb01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:46.244864+00:00
-- url     : https://prove2.me/submissions/e921f648-44bb-4600-8be6-e841bffe6705

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymStability
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymEvalOn_apply_f226649b2e6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_uniform_coeff_bound_56e632b89056
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.antisymEvalOn_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace AntisymStability
theorem _root_.solution (hB1 : AntisymDivisible.Statement) : AntisymStability.Statement := by
  intro T _ _ N j Om hOm
  set Ω : Set (T × Fin N → ℝ) :=
    ⋃ (τ : T) (a : Fin N) (b : Fin N) (_ : a.val < j ∧ j ≤ b.val), Om τ a b with hΩdef
  have hΩc : IsCompact Ω :=
    isCompact_iUnion fun τ => isCompact_iUnion fun a => isCompact_iUnion fun b =>
      isCompact_iUnion fun h => (hOm τ a b h.1 h.2).1
  have : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩc
  have : FiniteDimensional ℝ (homogeneousSubmodule (T × Fin N) ℝ (antisymDegree T N + 1)) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  have : FiniteDimensional ℝ (antisymSpace T N j) :=
    Submodule.finiteDimensional_of_le (fun P hP => hP.1)
  let Φ : antisymSpace T N j →ₗ[ℝ] C(Ω, ℝ) := (antisymEvalOn Ω).comp (antisymSpace T N j).subtype
  obtain ⟨g, hg⟩ := Φ.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict Φ)
  obtain ⟨C, hC0, hC⟩ := exists_uniform_coeff_bound (E := LinearMap.range Φ) ((antisymSpace T N j).subtype.comp g)
  refine ⟨C, fun P hP => ?_⟩
  let P' : antisymSpace T N j := ⟨P, hP⟩
  let y := Φ.rangeRestrict P'
  let Q : antisymSpace T N j := g y
  have hQ : Φ Q = Φ P' := by
    have h1 : Φ.rangeRestrict Q = y := LinearMap.congr_fun hg y
    exact congrArg Subtype.val h1
  have hker : Φ (P' - Q) = 0 := by rw [map_sub, hQ, sub_self]
  have hvan : ∀ x ∈ Ω, eval x ((P' - Q : antisymSpace T N j) : MvPolynomial (T × Fin N) ℝ) = 0 := by
    intro x hx
    have := congrArg (fun f : C(Ω, ℝ) => f ⟨x, hx⟩) hker
    simpa [Φ] using this
  obtain ⟨l, hl, hPl⟩ := hB1 T N j _ (P' - Q).2 (fun τ a b ha hb => by
    obtain ⟨_, _, O, hO, hne, hOsub⟩ := hOm τ a b ha hb
    refine ⟨O, hO, hne, fun x hx => hvan x ?_⟩
    exact Set.mem_iUnion.2 ⟨τ, Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b,
      Set.mem_iUnion.2 ⟨⟨ha, hb⟩, hOsub hx⟩⟩⟩⟩)
  refine ⟨l, hl, fun M hM hbd m => ?_⟩
  have hPQ : P - antisymDelta T N * l = (Q : MvPolynomial (T × Fin N) ℝ) := by
    rw [← hPl, Submodule.coe_sub]
    simp [P']
  rw [hPQ]
  have hy : ‖y‖ ≤ M := by
    have e : ‖y‖ = ‖Φ P'‖ := rfl
    rw [e, ContinuousMap.norm_le _ hM]
    rintro ⟨x, hx⟩
    have hx' := hx
    simp only [hΩdef, Set.mem_iUnion] at hx'
    obtain ⟨τ, a, b, ⟨ha, hb⟩, hxO⟩ := hx'
    simpa [Φ, P', Real.norm_eq_abs] using hbd τ a b ha hb x hxO
  calc |coeff m (Q : MvPolynomial (T × Fin N) ℝ)| ≤ C * ‖y‖ := hC y m
    _ ≤ C * M := mul_le_mul_of_nonneg_left hy hC0
end AntisymStability
end GroundTheory.Heights₂.Heights

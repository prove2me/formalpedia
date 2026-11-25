-- Prove2me | solution 1 for PI.DvRows.lattice_finitely_generated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:00:02.923615+00:00
-- url     : https://prove2.me/submissions/63f3c34c-9f4c-43a3-a3e5-917697350d46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_eq_zero_of_orth
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
namespace PI.DvRows
theorem _root_.solution : LamFG := by
  intro K _ _ _ _ _ A e n h hyp U _
  obtain ⟨-, hP, hH, -⟩ := hyp
  obtain ⟨hG, hn, hee, hnL, -⟩ := hP
  obtain ⟨-, ⟨S, hS⟩, hLsp⟩ := hG
  have htop : Submodule.span K ((S : Set A.V)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 K), hS]
    exact hLsp
  set m : A.V → A.V := fun g => ((n : ℕ) : 𝓞 K) • e g with hm
  have hmM : ∀ g ∈ (S : Set A.V), m g ∈ cutE A e A.L := by
    intro g hg
    refine ⟨hnL g (hS ▸ Submodule.subset_span hg), ?_⟩
    exact Submodule.smul_of_tower_mem _ _ (LinearMap.mem_range_self e g)
  have hint : ∀ y ∈ lamSub A e h U, ∀ g ∈ (S : Set A.V), IsIntegral ℤ (h (m g) y) := by
    intro y hy g hg
    obtain ⟨c, hc⟩ := hy.2.2 (m g) (hmM g hg)
    rw [hH.1 y (m g), ← hc]
    exact RingOfIntegers.isIntegral_coe (starO K c)
  let Φ : lamSub A e h U →ₗ[𝓞 K] (S → 𝓞 K) :=
    { toFun := fun y g => ⟨h (m g) y, hint y y.2 g g.2⟩
      map_add' := by
        intro y1 y2
        funext g
        apply RingOfIntegers.ext
        simp only [Submodule.coe_add, map_add]
        rfl
      map_smul' := by
        intro c y
        funext g
        apply RingOfIntegers.ext
        show h (m g) ((c • y : lamSub A e h U) : A.V) = (c : K) * h (m g) y
        rw [Submodule.coe_smul, ← algebraMap_smul K c (y : A.V), map_smul, smul_eq_mul] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    refine eq_zero_of_orth A e n h hH hee hn (S : Set A.V) htop y y.2.1 fun g hg => ?_
    have := congrFun hy ⟨g, hg⟩
    exact congrArg (fun t : 𝓞 K => (t : K)) this
  have : IsNoetherian (𝓞 K) (lamSub A e h U) := isNoetherian_of_injective Φ hinj
  exact (Submodule.fg_top _).1 (IsNoetherian.noetherian _)
end PI.DvRows

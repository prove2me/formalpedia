-- Prove2me | solution 1 for PI.LatLocGlob.Proof.exists_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:04.782921+00:00
-- url     : https://prove2.me/submissions/389b4e67-1623-4589-89d1-efe78acbbe07

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
import Theorems.Thm_PI_LatLocGlob_Proof_commonMult
import Theorems.Thm_PI_LatLocGlob_Proof_exists_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.LatLocGlob.Proof
theorem _root_.solution {N N' : Submodule R V} (hN : N.FG)
    (hN' : Submodule.span K (N' : Set V) = ⊤) : ∃ c : R, c ≠ 0 ∧ ∀ x ∈ N, c • x ∈ N' := by
  obtain ⟨s, rfl⟩ := hN
  obtain ⟨c, hc, hcs⟩ := commonMult (fun (g : V) (c : R) => c • g ∈ N')
    (fun g c d h => by rw [mul_smul]; exact N'.smul_mem d h) s
    (fun g _ => exists_smul_mem (K := K) N' (by rw [hN']; exact Submodule.mem_top))
  refine ⟨c, hc, fun x hx => ?_⟩
  have hle : Submodule.span R (s : Set V) ≤ N'.comap (c • LinearMap.id) := by
    rw [Submodule.span_le]
    intro g hg
    simpa using hcs g hg
  simpa using hle hx
end PI.LatLocGlob.Proof

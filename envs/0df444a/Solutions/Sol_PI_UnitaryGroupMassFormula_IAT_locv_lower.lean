-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IAT.locv_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:10.250613+00:00
-- url     : https://prove2.me/submissions/9c0b7ba0-f054-4acc-9fa2-4d65d64b4efe

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralityAtPrimeLattices_AwayLoc
import Theorems.Thm_Formalism_UG_P_adelstabL_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IAT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.IAT
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ w : Fin n → E ⊗[F] v.adicCompletion F, (∀ i, w i ∈ Formalism.L2.Geo.Def.PC.SV E v) →
      (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (m : E) * w i) ∈ Formalism.L2.Geo.Def.PC.latV v Λ := by
  classical
  have hk : ∀ k : Fin n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : Fin n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : Fin n → E) ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Σ k : Fin n, Fin (N k) => f p.1 p.2)
  have hsingle : ∀ k, (Pi.single k (m : E) : Fin n → E) ∈ Λ := by
    intro k
    have : (Pi.single k (m : E) : Fin n → E) =
        ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : Fin n → E) := by
      have h1 : (Pi.single k (m : E) : Fin n → E) = (m : E) • (Pi.single k 1 : Fin n → E) := by
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      rw [h1, ← hw k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul E, smul_smul]
      rfl
    rw [this]
    exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2
  refine ⟨m, hm0, fun y hy => ?_⟩
  have : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (m : E) * y i) =
      ∑ k, (⟨y k, hy k⟩ : Formalism.L2.Geo.Def.PC.SV E v) •
        (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : Fin n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = (_ : Formalism.L2.Geo.Def.PC.SV E v) •
        Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single i (m : E) : Fin n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, mul_comm]
    · intro k _ hki
      show (_ : Formalism.L2.Geo.Def.PC.SV E v) •
        Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : Fin n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [this]
  exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle k, rfl⟩)
end PI.UnitaryGroupMassFormula.IAT

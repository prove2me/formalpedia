-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IAT.locv_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:41.494604+00:00
-- url     : https://prove2.me/submissions/f65b7c4f-cdb5-41e6-b22b-f602a649bba8

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralityAtPrimeLattices_AwayLoc
import Theorems.Thm_PI_UnitaryGroupMassFormula_IAT_locv_incl_int
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_adelstabL_den
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
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IAT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.IAT
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ z ∈ Formalism.L2.Geo.Def.PC.latV v Λ, ∀ i,
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (m : E) * z i ∈ Formalism.L2.Geo.Def.PC.SV E v := by
  classical
  obtain ⟨t, ht⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : t × Fin n => (p.1 : Fin n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← ht] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  refine ⟨m, hm0, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    intro i
    rw [← map_mul]
    exact locv_incl_int v _ (hΛ x hx i)
  | zero => intro i; simp
  | add a b _ _ ha hb => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (ha i) (hb i)
  | smul s a _ ha =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 (ha i)
end PI.UnitaryGroupMassFormula.IAT

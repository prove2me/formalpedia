-- Prove2me | solution 1 for PI.WAU.exists_den_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:38.381697+00:00
-- url     : https://prove2.me/submissions/8c53ea42-4efd-4ba0-9365-b18778f659d7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Definitions.Def_Lemmata_GeneralBFactThirdMore_Key
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_exists_den_fin
import Theorems.Thm_PI_WAU_ohat_sum
import Theorems.Thm_PI_WAU_ohat_zsmul
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
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "Af" => FiniteAdeleRing (𝓞 F) F
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.WAU
theorem _root_.solution (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
  classical
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨p, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  obtain ⟨D, hD, h⟩ := exists_den_fin (fun q : Fin p × Fin n × ι => b.repr ((s q.1 : Fin n → E) q.2.1) q.2.2)
  refine ⟨D, hD, fun l hl j k => ?_⟩
  have hmem : (⟨l, hl⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hl' : l = ∑ t, c t • (s t : Fin n → E) := by
    have := congrArg Subtype.val hc
    simpa [Submodule.coe_sum] using this.symm
  have : (D : F) * b.repr (l j) k = ∑ t, c t • ((D : F) * b.repr ((s t : Fin n → E) j) k) := by
    rw [hl']
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [← b.coord_apply, map_sum]
    simp only [map_zsmul, b.coord_apply, Finset.mul_sum, mul_smul_comm, Finsupp.smul_apply]
  unfold IntF
  rw [this, map_sum]
  exact ohat_sum _ fun t _ => by rw [map_zsmul]; exact ohat_zsmul (h (t, j, k)) _
end PI.WAU

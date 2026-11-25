-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.stabClassFinite_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:39.288143+00:00
-- url     : https://prove2.me/submissions/be98ba52-b7fa-4184-bce7-4da31bbad959

import Definitions.Def_Formalism_PeriodIntegrals_InHHClassFin
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Theorems.Thm_Formalism_UG_Final_ClassSetFiniteL
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_SigConj
import Theorems.Thm_Formalism_UG_P_standard_lattice_full_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution (hMono : ClassSetMono) (hIdx : ClassSetFinIdx) (hMap : ClassSetMap)
    (hTop : KgNhd) (hSig : SigConj)
    (hR : ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)), DefiniteCompl I S → Restrict I S) :
    StabClassFinite := by
  intro I S hS K g x hg hK
  obtain ⟨g', hg', hg'K⟩ := hTop I g x hg
  have hCK : congS I S g' ≤ K := by
    rw [Subgroup.closure_le]
    intro h hh
    exact hK h (hg'K _ hh)
  apply hMono _ _ _ _ hCK
  obtain ⟨k, J', Φ, hH, hU, hD, hrat, hidx⟩ := hR I S hS
  apply hMap _ _ Φ
  rw [hrat]
  have hStd : Formalism.UG.CS.StdLatFull := by
    first
      | exact Formalism.UG.P.standard_lattice_full_holds
      | exact Formalism.UG.P.stdLatFull
      | exact Formalism.UG.P.stdLatFull_holds
      | exact Formalism.UG.P.CsEasy.stdLatFull
      | exact Formalism.UG.Final.StdLatFull
  obtain ⟨hfin, hspan⟩ := hStd I.E (Fin k)
  have hL := Formalism.UG.Final.ClassSetFiniteL I.F I.E (Fin k) I.cm.sig J' (hSig I) hH hU hD _ hfin hspan
  have h2 := hIdx _ _ _ _ inf_le_left (hidx g' hg') hL
  exact hMono _ _ _ _ inf_le_right h2
end PI.UnitaryGroupMassFormula.InHHClassFin

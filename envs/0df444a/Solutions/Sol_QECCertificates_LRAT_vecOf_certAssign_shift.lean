-- Prove2me | solution 1 for QECCertificates.LRAT.vecOf_certAssign_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:59.750812+00:00
-- url     : https://prove2.me/submissions/88d55a49-187d-4f92-90dd-050c6f73f531

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
public import Theorems.Thm_QECCertificates_LRAT_zmod2_indicator
public import Theorems.Thm_QECCertificates_LRAT_certAssign_mid

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {n : ℕ} (E w : Vec n) :
    vecOf (fun t => certAssign n E w (n + t)) n = w := by
  funext i
  have h1 : ¬ n + i.val < n := by omega
  have h2 : n + i.val < 2 * n := by omega
  have hfin : (⟨n + i.val - n, by omega⟩ : Fin n) = i :=
    Fin.ext (by change n + i.val - n = i.val; omega)
  rw [vecOf, certAssign_mid E w h1 h2, hfin]
  exact zmod2_indicator (w i)
end QECCertificates.LRAT

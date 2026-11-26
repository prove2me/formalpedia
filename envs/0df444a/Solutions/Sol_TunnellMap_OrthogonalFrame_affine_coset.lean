-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.affine_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:01.332814+00:00
-- url     : https://prove2.me/submissions/abe03db2-99bc-43cb-9ccb-27928db847bd

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_comm
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_OrthogonalFrame_decompose
import Theorems.Thm_TunnellMap_OrthogonalFrame_linComb3_injective
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift


attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.qForm_tau

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution (t : ℤ) (r : Triple) (hr : dot p r = t) :
    ∃! ab : ℤ × ℤ,
      r = linComb3 ab.1 ab.2 t F.e₁ F.e₂ F.z := by
  refine ⟨⟨F.coeff₁ r, F.coeff₂ r⟩, ?_, ?_⟩
  · have hd := F.decompose r
    have hcoeff : coeffZ (p := p) r = t := by
      rw [coeffZ, dot_comm, hr]
    rw [hcoeff] at hd
    exact hd.symm
  · rintro ⟨a, b⟩ hab
    have hcoeff : coeffZ (p := p) r = t := by
      rw [coeffZ, dot_comm, hr]
    have hrepr :
        r = linComb3 (F.coeff₁ r) (F.coeff₂ r) t F.e₁ F.e₂ F.z := by
      simpa [hcoeff] using (F.decompose r).symm
    have hlin :
        linComb3 a b t F.e₁ F.e₂ F.z =
          linComb3 (F.coeff₁ r) (F.coeff₂ r) t F.e₁ F.e₂ F.z := by
      exact hab.symm.trans hrepr
    have habc : (a, (b, t)) = (F.coeff₁ r, (F.coeff₂ r, t)) :=
      F.linComb3_injective hlin
    exact congrArg (fun abc : ℤ × ℤ × ℤ => (abc.1, abc.2.1)) habc
end TunnellMap.OrthogonalFrame

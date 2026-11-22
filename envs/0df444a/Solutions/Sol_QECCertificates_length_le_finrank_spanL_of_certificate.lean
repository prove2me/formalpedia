-- Prove2me | solution 1 for QECCertificates.length_le_finrank_spanL_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:19.657816+00:00
-- url     : https://prove2.me/submissions/09e3edaa-df66-46b2-a487-ed23914f1cbd

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_linearIndependent_get_of_echelon
public import Theorems.Thm_QECCertificates_range_get_eq_rowList


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {L : List (Vec n)} {D : List (PivRow n)}
    (hsub : ∀ i : Fin D.length, (D.get i).1 ∈ spanL L)
    (h1 : EchSelf D) (h2 : EchPair D) :
    D.length ≤ Module.finrank (ZMod 2) (spanL L) := by
  have hcard := finrank_span_eq_card (linearIndependent_get_of_echelon h1 h2)
  rw [range_get_eq_rowList] at hcard
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList D)) = Fintype.card (Fin D.length) := hcard
  rw [Fintype.card_fin] at hcard'
  have hle : spanL (rowList D) ≤ spanL L := by
    rw [spanL, Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact hsub i
  calc D.length = Module.finrank (ZMod 2) (spanL (rowList D)) := hcard'.symm
    _ ≤ Module.finrank (ZMod 2) (spanL L) := Submodule.finrank_mono hle
end QECCertificates

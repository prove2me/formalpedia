-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_chain_cffe35f4d0ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:12:01.154199+00:00
-- url     : https://prove2.me/submissions/4a52493e-aa63-4002-86de-04a13546ecd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isGradedSub_sup_b38159db1f45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_step_90568b34aa57

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
theorem _root_.solution [Module.Finite (MRing ι F) M] (hM : IsMultigrading ι M piece) :
    ∀ N₀ : Submodule (MRing ι F) M, IsGradedSub piece N₀ →
      ∃ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
        (q : Fin n → Ideal (MRing ι F)),
        N 0 = N₀ ∧ N (Fin.last n) = ⊤ ∧
        ∀ j : Fin n, x j ∈ piece (c j) ∧
          N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
          (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
          ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j := by
  haveI : IsNoetherian (MRing ι F) M := inferInstance
  haveI : WellFoundedGT (Submodule (MRing ι F) M) := isNoetherian_iff'.mp inferInstance
  intro N₀
  induction N₀ using WellFoundedGT.induction with
  | _ N₀ ih =>
  intro hN₀
  by_cases ht : N₀ = ⊤
  · exact ⟨0, fun _ => N₀, Fin.elim0, Fin.elim0, Fin.elim0, rfl, ht, fun j => j.elim0⟩
  obtain ⟨c, x, hx, hxN, hq, hqh⟩ := exists_step hM hN₀ ht
  have hlt : N₀ < N₀ ⊔ Submodule.span (MRing ι F) {x} := by
    refine lt_of_le_of_ne le_sup_left fun h => hxN ?_
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  obtain ⟨n, N, x', c', q', h0, hl, hj⟩ := ih _ hlt (isGradedSub_sup hM hN₀ hx)
  refine ⟨n + 1, Fin.cons N₀ N, Fin.cons x x', Fin.cons c c', Fin.cons (N₀.colon {x}) q', rfl,
    ?_, fun j => ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hl
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ]
      exact ⟨hx, h0, hq, hqh, fun s => Submodule.mem_colon_singleton.symm⟩
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      exact hj j
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration

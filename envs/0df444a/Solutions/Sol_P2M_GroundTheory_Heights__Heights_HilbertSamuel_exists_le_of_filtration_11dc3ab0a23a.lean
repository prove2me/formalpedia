-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_le_of_filtration_11dc3ab0a23a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:12.352446+00:00
-- url     : https://prove2.me/submissions/384d26ac-189a-43fb-a4ff-335ba7e83497

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PModulesFromPrimes

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (x : Fin n → M) (q : Fin n → Ideal R)
    (h0 : N 0 = ⊥) (htop : N (Fin.last n) = ⊤)
    (hstep : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span R {x j} ∧
      ∀ s : R, s • x j ∈ N j.castSucc ↔ s ∈ q j)
    (p : Ideal R) [hp : p.IsPrime] (hann : Module.annihilator R M ≤ p) : ∃ j, q j ≤ p := by
  by_contra hne
  push Not at hne
  have hs : ∀ j, ∃ s ∈ q j, s ∉ p := fun j => Set.not_subset.mp (hne j)
  choose s hsq hsp using hs
  have key : ∀ i (hi : i < n + 1), ∃ t ∉ p, ∀ y ∈ N ⟨i, hi⟩, t • y = 0 := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun y hy => ?_⟩
      rw [show (⟨0, hi⟩ : Fin (n + 1)) = 0 from Fin.ext (by simp), h0, Submodule.mem_bot] at hy
      simp [hy]
    | succ i ih =>
      intro hi
      obtain ⟨t, htp, ht⟩ := ih (by omega)
      let j : Fin n := ⟨i, by omega⟩
      refine ⟨t * s j, fun hm => (hp.mem_or_mem hm).elim htp (hsp j), fun y hy => ?_⟩
      have hy' : y ∈ N j.succ := hy
      rw [(hstep j).1, Submodule.mem_sup] at hy'
      obtain ⟨z, hz, w, hw, rfl⟩ := hy'
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have h1 : s j • (z + r • x j) ∈ N j.castSucc := by
        rw [smul_add, smul_comm (s j) r (x j)]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hz)
          (Submodule.smul_mem _ _ (((hstep j).2 _).2 (hsq j)))
      rw [mul_smul]
      exact ht _ h1
  obtain ⟨t, htp, ht⟩ := key n (Nat.lt_succ_self n)
  apply htp
  apply hann
  rw [Module.mem_annihilator]
  intro y
  apply ht
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, htop]
  trivial
end GroundTheory.Heights₂.Heights.HilbertSamuel

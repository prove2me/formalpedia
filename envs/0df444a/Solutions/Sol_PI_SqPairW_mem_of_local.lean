-- Prove2me | solution 1 for PI.SqPairW.mem_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:12.52333+00:00
-- url     : https://prove2.me/submissions/de928e43-6327-4fe8-a494-9e40174f5bda

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution {V : Type*} [AddCommGroup V] (Y : AddSubgroup V) (x : V)
    (h : ∀ p : ℕ, p.Prime → ∃ t : ℤ, ¬ (p : ℤ) ∣ t ∧ t • x ∈ Y) : x ∈ Y := by
  classical
  let I : Ideal ℤ :=
    { carrier := {t | t • x ∈ Y}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • x ∈ Y
        rw [add_smul]
        exact Y.add_mem ha hb
      zero_mem' := by
        show (0 : ℤ) • x ∈ Y
        rw [zero_smul]
        exact Y.zero_mem
      smul_mem' := fun c {t} ht => by
        show (c • t) • x ∈ Y
        rw [smul_eq_mul, mul_smul]
        exact Y.zsmul_mem ht c }
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmem : ∀ t : ℤ, t • x ∈ Y ↔ n ∣ t := by
    intro t
    have e : t ∈ I ↔ t ∈ Submodule.span ℤ {n} := by rw [hn]
    exact e.trans Ideal.mem_span_singleton
  have h1 : n ∣ 1 := by
    by_contra hn1
    have hna : n.natAbs ≠ 1 := by
      intro e
      apply hn1
      rw [← Int.natAbs_dvd, e]
      exact one_dvd _
    have hp := Nat.minFac_prime hna
    obtain ⟨t, ht, htY⟩ := h _ hp
    apply ht
    have hpn : ((n.natAbs.minFac : ℕ) : ℤ) ∣ n := Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)
    exact hpn.trans ((hmem t).1 htY)
  have := (hmem 1).2 h1
  rwa [one_smul] at this
end PI.SqPairW

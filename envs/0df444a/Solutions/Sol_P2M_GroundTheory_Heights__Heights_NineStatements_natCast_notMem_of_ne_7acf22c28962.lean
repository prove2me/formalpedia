-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_natCast_notMem_of_ne_7acf22c28962
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:07.647871+00:00
-- url     : https://prove2.me/submissions/5b626b6a-4657-47ea-9457-81f027fe6c91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {L : Type} [Field L] [NumberField L] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (𝔓 : HeightOneSpectrum (𝓞 L)) (h : (p : 𝓞 L) ∈ 𝔓.asIdeal) : (q : 𝓞 L) ∉ 𝔓.asIdeal := by
  intro hq'
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  apply 𝔓.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((u * p + v * q : ℤ) : 𝓞 L) = 1 := by rw [huv]; simp
  rw [← h1]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hq')
end GroundTheory.Heights₂.Heights.NineStatements

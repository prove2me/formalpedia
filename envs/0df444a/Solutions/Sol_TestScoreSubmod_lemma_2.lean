-- Prove2me | solution 1 for TestScoreSubmod.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:44:40.114807+00:00
-- url     : https://prove2.me/submissions/310e1520-dd96-454f-bc57-fb55838f077f

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (u vl vu : Finset ι → ℝ) (p q : ℝ)
    (k : ℕ) (hk : 0 < k)
    (hu0 : ∀ S, 0 ≤ u S) (humono : Monotone u) (husub : NonmonotoneSubmod.Shared.Submodular u)
    (hp : 0 < p) (hq : 0 ≤ q)
    (hlow : ∀ S : Finset ι, S.card = k → p * vl S ≤ u S)
    (hup : ∀ S : Finset ι, S.Nonempty → S.card ≤ k → u S ≤ q * vu S)
    (Sstar : Finset ι) (hSstar : Sstar.card = k)
    (hb : ∀ R : Finset ι, R.Nonempty → Disjoint R Sstar → R.card ≤ k →
      ∃ T : Finset ι, R ⊆ T ∧ Disjoint T Sstar ∧ T.card ≤ k ∧ vu T ≤ vl Sstar) :
    ∀ O : Finset ι, O.card = k → p / (q + p) * u O ≤ u Sstar := by
  intro O hO
  have hqp : 0 < q + p := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hqp]
  have hsub : O ⊆ Sstar ∪ (O \ Sstar) := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h1 : u O ≤ u (Sstar ∪ (O \ Sstar)) := humono hsub
  rcases (O \ Sstar).eq_empty_or_nonempty with hR | hR
  · rw [hR, Finset.union_empty] at h1
    have := hu0 O
    nlinarith
  · have hdisj : Disjoint (O \ Sstar) Sstar := Finset.sdiff_disjoint
    have hcard : (O \ Sstar).card ≤ k := hO ▸ Finset.card_le_card Finset.sdiff_subset
    obtain ⟨T, hRT, -, hTk, hvT⟩ := hb (O \ Sstar) hR hdisj hcard
    have h2 := husub Sstar (O \ Sstar)
    have hinter : Sstar ∩ (O \ Sstar) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_sdiff)
    rw [hinter] at h2
    have h0 := hu0 ∅
    have h3 : u (O \ Sstar) ≤ u T := humono hRT
    have h4 : u T ≤ q * vu T := hup T (hR.mono hRT) hTk
    have h5 : q * vu T ≤ q * vl Sstar := mul_le_mul_of_nonneg_left hvT hq
    have h6 := hlow Sstar hSstar
    have hchain : u O ≤ u Sstar + q * vl Sstar := by linarith
    have hm1 := mul_le_mul_of_nonneg_left hchain hp.le
    have hm2 := mul_le_mul_of_nonneg_left h6 hq
    nlinarith

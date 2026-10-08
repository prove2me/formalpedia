-- Prove2me | solution 1 for RobustPower.AdaptGap.lemma_2_3_center
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:53:07.499984+00:00
-- url     : https://prove2.me/submissions/edbe1869-626b-4b79-a2e5-4f151ce80a29

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_SymmetricSets

open Matrix RobustPower.AdaptGap

private theorem reflect_mem {E : Type*} [AddCommGroup E] {S : Set E} {u x : E}
    (hsym : RobustPower.StochGap.IsSymmetricAbout S u) (hx : x ∈ S) :
    u - (x - u) ∈ S := by
  apply (hsym.2 (x - u)).mp
  simpa only [add_sub_cancel] using hx

/-- Lemma 2.3, p. 12: for a bounded set `S` symmetric about `u` (boundedness is implicit on the
page in the maxima and minima (2.5)–(2.6)), the centre of the bounding hypercube (2.7) is `u`.
If moreover `S ⊆ ℝⁿ₊` (the paper's setting, used by its proof; the printed second claim fails
for `S = [-1, 1]`), then `x ≤ 2 · x⁰` for all `x ∈ S`. -/
theorem solution {ι : Type*} [Fintype ι] (S : Set (ι → ℝ))
    (u : ι → ℝ) (hsym : RobustPower.StochGap.IsSymmetricAbout S u)
    (hbdd : Bornology.IsBounded S) :
    boxCenter S = u ∧
      ((∀ x ∈ S, 0 ≤ x) → ∀ x ∈ S, x ≤ (2 : ℝ) • boxCenter S) := by
  have hcenter : boxCenter S = u := by
    funext j
    let T : Set ℝ := (fun x : ι → ℝ => x j) '' S
    have hne : T.Nonempty := ⟨u j, u, hsym.1, rfl⟩
    have hlo : BddBelow T := by
      obtain ⟨l, hl⟩ := hbdd.bddBelow
      exact ⟨l j, by rintro _ ⟨x, hx, rfl⟩; exact hl hx j⟩
    have hhi : BddAbove T := by
      obtain ⟨h, hh⟩ := hbdd.bddAbove
      exact ⟨h j, by rintro _ ⟨x, hx, rfl⟩; exact hh hx j⟩
    have hr : ∀ t ∈ T, 2 * u j - t ∈ T := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨u - (x - u), reflect_mem hsym hx, ?_⟩
      simp only [Pi.sub_apply]
      ring
    have ha : sSup T ≤ 2 * u j - sInf T := by
      apply csSup_le hne
      intro t ht
      have := csInf_le hlo (hr t ht)
      linarith
    have hb : 2 * u j - sSup T ≤ sInf T := by
      apply le_csInf hne
      intro t ht
      have := le_csSup hhi (hr t ht)
      linarith
    change (sInf T + sSup T) / 2 = u j
    linarith
  refine ⟨hcenter, ?_⟩
  intro hn x hx j
  have h := hn (u - (x - u)) (reflect_mem hsym hx) j
  rw [hcenter]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply] at h ⊢
  linarith

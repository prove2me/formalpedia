-- Prove2me | solution 1 for RestrictedAP.Counting.proposition_5_28_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:33:53.814859+00:00
-- url     : https://prove2.me/submissions/cfc288af-604a-4870-8ea7-99bd42068bed

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Theorems.Thm_RestrictedAP_Counting_proposition_5_28_atoms

open ComplexOrder
set_option autoImplicit false

namespace RestrictedAP.Counting

private lemma psd_gap_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) {a b : ℝ} (hab : a ≤ b)
    (h : (M - (b : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef) :
    (M - (a : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
  have hd : (((b - a : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (Complex.zero_le_real.2 (sub_nonneg.2 hab))
  have heq : M - (a : ℂ) • (1 : Matrix ι ι ℂ) =
      (M - (b : ℂ) • (1 : Matrix ι ι ℂ)) + ((b - a : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [heq]
  exact h.add hd

open Matrix in
theorem chk_proposition_5_28_uniform (m : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (q' : ℕ), q' + 1 ≤ m →
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig = q' + 1 →
      ∀ μ : Sig × Sig × Sig → ℝ, IsDist μ → ¬ DistHasEmbedding ℤ μ → AtomsAtLeast μ s →
        (∀ (i : Fin 3) (a : Sig), marginal μ i a ≠ 0) →
      ∀ fb : Fin 3 → Fin (q' + 1) → Sig → ℂ,
        (∀ i a, fb i 0 a = 1) →
        (∀ (i : Fin 3) (j k : Fin (q' + 1)),
          ∑ a, (marginal μ i a : ℂ) * star (fb i j a) * fb i k a = if j = k then 1 else 0) →
        let W : Fin 3 × Fin q' → Sig × Sig × Sig → ℂ :=
          fun ij t => fb ij.1 ij.2.succ (coord3 ij.1 t)
        let Mcov : Matrix (Fin 3 × Fin q') (Fin 3 × Fin q') ℂ :=
          Matrix.of fun ij kl => ∑ t, (μ t : ℂ) * W ij t * star (W kl t)
        Mcov.PosDef ∧
          (Mcov - (η : ℂ) • (1 : Matrix (Fin 3 × Fin q') (Fin 3 × Fin q') ℂ)).PosSemidef := by
  classical
  choose ef hefp hef using fun q' => proposition_5_28_atoms q' s hs
  by_cases hm : m = 0
  · subst m
    exact ⟨1, one_pos, fun q' hq => by omega⟩
  let inds : Finset ℕ := Finset.range m
  have hne : inds.Nonempty := ⟨0, Finset.mem_range.2 (Nat.pos_of_ne_zero hm)⟩
  let η := inds.inf' hne ef
  have hηp : 0 < η := (Finset.lt_inf'_iff hne).2 (fun q' _ => hefp q')
  refine ⟨η, hηp, ?_⟩
  intro q' hq Sig _ _ hcard μ hμ hemb hat hmar fb hfb0 horth W Mcov
  have hmem : q' ∈ inds := Finset.mem_range.2 (Nat.lt_of_succ_le hq)
  have hηle : η ≤ ef q' := Finset.inf'_le ef hmem
  obtain ⟨hpd, hpsd⟩ := hef q' Sig hcard μ hμ hemb hat hmar fb hfb0 horth
  exact ⟨hpd, psd_gap_mono Mcov hηle hpsd⟩

end RestrictedAP.Counting

theorem solution : type_of% @RestrictedAP.Counting.chk_proposition_5_28_uniform :=
  @RestrictedAP.Counting.chk_proposition_5_28_uniform

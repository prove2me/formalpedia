-- Prove2me | solution 1 for StochFictPlay.Potential.lemmaA5_exists_player
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:23:21.792572+00:00
-- url     : https://prove2.me/submissions/b6b6cf78-f78a-42e3-90c6-199b5e28a8b3

import Mathlib
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_Stability

set_option autoImplicit false

namespace StochFictPlay.Potential

theorem lemmaA5_key_e17744f2 {N : ℕ} (v : Fin N → ℝ)
    (hne : (Finset.univ : Finset (Fin N)).Nonempty) (hs : ∑ i, v i = 0)
    (q : ℝ) (hq : 0 < q) (hS : 1 ≤ q * ∑ i, v i ^ 2) :
    1 / ((N : ℝ) * Real.sqrt q) < Finset.univ.sup' hne v ∧
      Finset.univ.inf' hne v < -(1 / ((N : ℝ) * Real.sqrt q)) := by
  set M := Finset.univ.sup' hne v with hMdef
  set m := Finset.univ.inf' hne v with hmdef
  have hM : ∀ i, v i ≤ M := fun i => Finset.le_sup' v (Finset.mem_univ i)
  have hm : ∀ i, m ≤ v i := fun i => Finset.inf'_le v (Finset.mem_univ i)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_inf' hne v
  obtain ⟨i1, -, hi1⟩ := Finset.exists_mem_eq_sup' hne v
  set S := ∑ i, v i ^ 2 with hSdef
  have h1 : 0 ≤ ∑ i, (v i - m) * (M - v i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.2 (hm i)) (sub_nonneg.2 (hM i)))
  have e1 : ∑ i, (v i - m) * (M - v i) = ∑ i, ((M + m) * v i - v i ^ 2 - m * M) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 : M - v i0 ≤ ∑ i, (M - v i) :=
    Finset.single_le_sum (f := fun i => M - v i) (fun i _ => sub_nonneg.2 (hM i))
      (Finset.mem_univ i0)
  rw [Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← hi0] at h2
  have h3 : v i1 - m ≤ ∑ i, (v i - m) :=
    Finset.single_le_sum (f := fun i => v i - m) (fun i _ => sub_nonneg.2 (hm i))
      (Finset.mem_univ i1)
  rw [Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← hi1] at h3
  have hmM : m ≤ M := le_trans (hm i0) (hM i0)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- q * N * (-m) * M ≥ 1
  have ha : 1 ≤ q * ((N : ℝ) * ((-m) * M)) := by
    have : S ≤ (N : ℝ) * ((-m) * M) := by linarith
    calc 1 ≤ q * S := hS
      _ ≤ q * ((N : ℝ) * ((-m) * M)) := mul_le_mul_of_nonneg_left this hq.le
  have hprod : 0 < (N : ℝ) * ((-m) * M) := by
    by_contra h
    replace h := not_lt.mp h
    have : q * ((N : ℝ) * ((-m) * M)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le h
    linarith
  have hNpos : (0 : ℝ) < N := by
    rcases lt_or_eq_of_le hN0 with h | h
    · exact h
    · rw [← h] at hprod; simp at hprod
  have hmMpos : 0 < (-m) * M := by
    by_contra h
    replace h := not_lt.mp h
    have : (N : ℝ) * ((-m) * M) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 h
    linarith
  have hMpos : 0 < M := by
    by_contra h
    replace h := not_lt.mp h
    have : 0 ≤ -m := by linarith
    have : (-m) * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos this h
    linarith
  have hmneg : 0 < -m := by
    by_contra h
    replace h := not_lt.mp h
    have : (-m) * M ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hMpos.le
    linarith
  -- -m ≤ (N-1) M and M ≤ (N-1)(-m)
  have hb : -m ≤ ((N : ℝ) - 1) * M := by linarith
  have ha' : M ≤ ((N : ℝ) - 1) * (-m) := by linarith
  set s := Real.sqrt q with hsdef
  have hs2 : s ^ 2 = q := Real.sq_sqrt hq.le
  have hspos : 0 < s := Real.sqrt_pos.2 hq
  have hNs : 0 < (N : ℝ) * s := mul_pos hNpos hspos
  -- M^2 * (N-1) ≥ (-m) M, so q N (N-1) M^2 ≥ 1
  have hM2 : 1 ≤ q * (N : ℝ) * (((N : ℝ) - 1) * M ^ 2) := by
    have : (-m) * M ≤ ((N : ℝ) - 1) * M ^ 2 := by nlinarith
    have hqN : 0 ≤ q * (N : ℝ) := by positivity
    calc (1 : ℝ) ≤ q * ((N : ℝ) * ((-m) * M)) := ha
      _ = q * (N : ℝ) * ((-m) * M) := by ring
      _ ≤ q * (N : ℝ) * (((N : ℝ) - 1) * M ^ 2) := mul_le_mul_of_nonneg_left this hqN
  have hm2 : 1 ≤ q * (N : ℝ) * (((N : ℝ) - 1) * (-m) ^ 2) := by
    have : (-m) * M ≤ ((N : ℝ) - 1) * (-m) ^ 2 := by nlinarith
    have hqN : 0 ≤ q * (N : ℝ) := by positivity
    calc (1 : ℝ) ≤ q * ((N : ℝ) * ((-m) * M)) := ha
      _ = q * (N : ℝ) * ((-m) * M) := by ring
      _ ≤ q * (N : ℝ) * (((N : ℝ) - 1) * (-m) ^ 2) := mul_le_mul_of_nonneg_left this hqN
  have hqNM : 0 < q * (N : ℝ) * M ^ 2 := by positivity
  have hqNm : 0 < q * (N : ℝ) * (-m) ^ 2 := by positivity
  -- (M N s)^2 = N * (q N M^2) > (N-1) q N M^2 ≥ 1
  have tM : 1 < (M * ((N : ℝ) * s)) ^ 2 := by
    have : (M * ((N : ℝ) * s)) ^ 2 = (N : ℝ) * (q * (N : ℝ) * M ^ 2) := by
      rw [← hs2]; ring
    rw [this]
    nlinarith
  have tm : 1 < ((-m) * ((N : ℝ) * s)) ^ 2 := by
    have : ((-m) * ((N : ℝ) * s)) ^ 2 = (N : ℝ) * (q * (N : ℝ) * (-m) ^ 2) := by
      rw [← hs2]; ring
    rw [this]
    nlinarith
  have pM : 0 < M * ((N : ℝ) * s) := mul_pos hMpos hNs
  have pm : 0 < (-m) * ((N : ℝ) * s) := mul_pos hmneg hNs
  have gM : 1 < M * ((N : ℝ) * s) := by nlinarith
  have gm : 1 < (-m) * ((N : ℝ) * s) := by nlinarith
  constructor
  · rw [div_lt_iff₀ hNs]; exact gM
  · have : 1 / ((N : ℝ) * s) < -m := by rw [div_lt_iff₀ hNs]; exact gm
    linarith

end StochFictPlay.Potential

open StochFictPlay.Potential in
theorem solution (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (θ : Mixed n) (hθ : θ ∈ unitTangent n) :
    ∃ β : Fin p,
      1 / ((n β : ℝ) * Real.sqrt p) <
          Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn β⟩⟩) (θ β) ∧
        Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn β⟩⟩) (θ β) <
          -(1 / ((n β : ℝ) * Real.sqrt p)) := by
  have h0 : ∀ α, ∑ i, θ α i = 0 := hθ.1
  have hsum : ∑ α, ∑ i, θ α i ^ 2 = 1 := hθ.2
  have hne : (Finset.univ : Finset (Fin p)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨β, -, hβ⟩ := Finset.exists_max_image Finset.univ (fun α => ∑ i, θ α i ^ 2) hne
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  refine ⟨β, StochFictPlay.Potential.lemmaA5_key_e17744f2 (θ β) _ (h0 β) (p : ℝ) hp0 ?_⟩
  calc (1 : ℝ) = ∑ α, ∑ i, θ α i ^ 2 := hsum.symm
    _ ≤ ∑ _α : Fin p, ∑ i, θ β i ^ 2 := Finset.sum_le_sum (fun α _ => hβ α (Finset.mem_univ _))
    _ = (p : ℝ) * ∑ i, θ β i ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

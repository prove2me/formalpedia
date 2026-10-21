-- Prove2me | solution 1 for QRH.prime_extraction
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:17:39.614951+00:00
-- url     : https://prove2.me/submissions/6c305324-4bcc-46f2-a806-de83481fc0be

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun
universe u

open QRH

/-- The one-element arithmetic world with no primes. -/
abbrev g59W : QRHWorld.{u} where
  E := PUnit
  mul := fun _ _ => PUnit.unit
  one := PUnit.unit
  mul_assoc := fun _ _ _ => rfl
  mul_comm := fun _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl
  wpow := fun _ _ => PUnit.unit
  wpow_zero := fun _ => rfl
  wpow_succ := fun _ _ => rfl
  wpow_mul := fun _ _ _ => rfl
  IsSqf := fun _ => True
  sqf_one := trivial
  Sgood := fun _ => True
  Sgood_one := trivial
  Sgood_mul := fun _ _ _ _ => trivial
  Sgood_wpow := fun _ _ _ => trivial
  IsP := fun _ => False
  prime_sqf := fun _ h => h.elim
  prime_sgood := fun _ h => h.elim
  pow6_inj := fun _ _ h => h.elim
  N := fun _ => 1
  N_pos := fun _ => one_pos
  N_one := rfl
  N_mul := fun _ _ => (one_mul 1).symm
  N_wpow := fun _ k => (one_pow k).symm
  divs := fun _ => {PUnit.unit}
  divs_refl := fun _ => Finset.mem_singleton_self _
  divs_one := fun _ _ => rfl
  divs_mul := fun _ _ _ _ _ _ => Finset.mem_singleton_self _
  coDiv := fun _ _ => PUnit.unit
  codiv_mul := fun _ _ _ => rfl
  codiv_mem := fun _ _ _ => Finset.mem_singleton_self _
  codiv_invol := fun _ _ _ => rfl
  mu := fun _ => 1
  mu_inversion_one := by simp
  mu_inversion_ne := fun b hb => (hb rfl).elim
  mu_sqf := fun _ _ => one_mul 1
  mu_zero := fun _ h => (h trivial).elim
  chi := fun _ _ => 1
  chi_mul_den := fun _ _ _ => (one_mul 1).symm
  chi_mul_num := fun _ _ _ => (one_mul 1).symm
  chi_one_num := fun _ => rfl
  chi_triv := fun _ _ => Or.inr (by simp)
  chi_sixth_mem := fun _ _ h => h.elim
  chi_sixth_coprime := fun _ _ h => h.elim
  recip_cubic := fun _ _ => rfl
  alpha := fun _ => 1
  alpha_mul := fun _ _ => (one_mul 1).symm
  alpha_abs := fun _ => by simp
  C := PUnit
  mulC := fun _ _ => PUnit.unit
  oneC := PUnit.unit
  invC := fun _ => PUnit.unit
  mulC_assoc := fun _ _ _ => rfl
  mulC_comm := fun _ _ => rfl
  oneC_mul := fun _ => rfl
  mulC_one := fun _ => rfl
  invC_mul_cancel := fun _ => rfl
  mulC_inv_cancel := fun _ => rfl
  mulC_inv := fun _ _ => rfl
  cl := fun _ => PUnit.unit
  cl_mul := fun _ _ => rfl
  cl_one := rfl
  Rcl := fun _ _ => 1
  Rcl_abs := fun _ _ => by simp
  Rcl_real := fun _ _ => Or.inl rfl
  Rcl_symm := fun _ _ => rfl
  Rcl_mul_left := fun _ _ _ => (one_mul 1).symm
  Rcl_mul_right := fun _ _ _ => (one_mul 1).symm
  Rcl_one_left := fun _ => rfl
  Rcl_one_right := fun _ => rfl
  chiNeg := fun _ => 1
  chiNeg_abs := fun _ => by simp
  Gcl := fun _ => 1
  Gcl_abs := fun _ => by simp
  Gcl_mul := fun _ _ => by simp
  Gcl_invC := fun _ => by simp
  gamma := fun _ _ => 1
  gamma_abs := fun _ _ _ _ => by simp
  gamma_2_cube := fun _ _ _ => by simp
  gamma_1_2 := fun _ _ _ => by simp
  gamma_1_m1 := fun _ _ _ => by simp
  gamma_2_mul := fun _ _ _ _ _ _ _ => by simp
  xi := fun _ => 1
  xi_mul := fun _ _ => (one_mul 1).symm
  xi_one := rfl

open Classical in
noncomputable def g59S : QRHSums g59W.{u} where
  fin := fun X => if 1 ≤ X then {PUnit.unit} else ∅
  fin_spec := fun X n => by
    by_cases h : (1:ℝ) ≤ X
    · rw [if_pos h]; exact ⟨fun _ => ⟨trivial, h⟩, fun _ => Finset.mem_singleton.2 rfl⟩
    · rw [if_neg h]; exact ⟨fun h' => absurd h' (Finset.notMem_empty _), fun h' => (h h'.2).elim⟩
  primeRange := fun _ => ∅
  primeRange_spec := fun _ _ => ⟨fun h' => absurd h' (Finset.notMem_empty _), fun h' => h'.1.elim⟩
  divBy := fun _ X => if 1 ≤ X then {PUnit.unit} else ∅
  divBy_spec := fun p n X => by
    by_cases h : (1:ℝ) ≤ X
    · rw [if_pos h]
      exact ⟨fun _ => ⟨Finset.mem_singleton.2 rfl, trivial, h⟩, fun _ => Finset.mem_singleton.2 rfl⟩
    · rw [if_neg h]; exact ⟨fun h' => absurd h' (Finset.notMem_empty _), fun h' => (h h'.2.2).elim⟩
  cdiv := 0
  count_divisor := fun _ _ h => h.elim
  cL := 0
  landau := fun _ _ => by simp
  dyad := fun F => if F ≤ 1 ∧ 1 < 2 * F then {PUnit.unit} else ∅
  dyad_spec := fun F f => by
    by_cases h : F ≤ 1 ∧ 1 < 2 * F
    · rw [if_pos h]; exact ⟨fun _ => h, fun _ => Finset.mem_singleton.2 rfl⟩
    · rw [if_neg h]; exact ⟨fun h' => absurd h' (Finset.notMem_empty _), fun h' => (h h').elim⟩
  sqfs := fun X => if 1 ≤ X then {PUnit.unit} else ∅
  sqfs_spec := fun X n => by
    by_cases h : (1:ℝ) ≤ X
    · rw [if_pos h]
      exact ⟨fun _ => ⟨trivial, trivial, h⟩, fun _ => Finset.mem_singleton.2 rfl⟩
    · rw [if_neg h]; exact ⟨fun h' => absurd h' (Finset.notMem_empty _), fun h' => (h h'.2.2).elim⟩

lemma g59_A (c : g59W.{u}.E → ℂ) (Wt : ℝ → ℂ) (u0 : g59W.{u}.E) {D X : ℝ} (hX : 1 ≤ X) :
    Asum g59W g59S c u0 Wt D X = c PUnit.unit * Wt (1 / D) := by
  simp [Asum, g59S, hX, g59W]

theorem solution : ¬ (∀ (W : QRHWorld.{0}) (S : QRHSums W)
    (c : W.E → ℂ) (Wt : ℝ → ℂ)
    (hcb : ∀ n : W.E, W.Sgood n → ‖c n‖ ≤ 1)
    (θ ε : ℝ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1 / 10) (hε : 0 < ε)
    (hms : ∃ k : ℝ, ∀ D : ℝ, 2 ≤ D →
      msSum W S c Wt (D ^ (1 + θ)) D (2 * D) ≤ k * D ^ (2 + θ + ε)),
    ∃ k : ℝ, ∀ D : ℝ, 2 ≤ D →
      ‖A1sum W S c Wt D (2 * D)‖
        ≤ k * D ^ (11 / 12 + 5 * θ / 12 + ε)) := by
  intro h
  set Wt : ℝ → ℂ := fun x => ((1 / x : ℝ) : ℂ) with hWt
  have hA : ∀ D : ℝ, 2 ≤ D → ∀ u0, ∀ X : ℝ, 1 ≤ X →
      ‖Asum g59W.{0} g59S (fun _ => 1) u0 Wt D X‖ = D := by
    intro D hD u0 X hX
    rw [g59_A _ _ _ hX]
    simp only [hWt, one_mul, one_div, inv_inv]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  obtain ⟨k, hk⟩ := h g59W.{0} g59S (fun _ => 1) Wt (fun _ _ => by simp) (1 / 10) (1 / 48)
    (by norm_num) le_rfl (by norm_num) ⟨1, fun D hD => by
      have hH : (1:ℝ) ≤ D ^ (1 + 1 / 10 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have hms : msSum g59W.{0} g59S (fun _ => 1) Wt (D ^ (1 + 1 / 10 : ℝ)) D (2 * D) = D ^ 2 := by
        have hfin : (g59S.{0}).fin (D ^ (1 + 1 / 10 : ℝ)) = {PUnit.unit} := if_pos hH
        unfold msSum
        rw [hfin, Finset.sum_singleton, hA D hD _ _ (by linarith)]
      rw [hms, one_mul]
      have : D ^ (2:ℝ) ≤ D ^ (2 + 1 / 10 + 1 / 48 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      exact_mod_cast this⟩
  -- D ≤ k D^(47/48) for all D ≥ 2: contradiction
  set D : ℝ := max 2 ((|k| + 1) ^ (48 : ℕ)) with hD
  have hD2 : 2 ≤ D := le_max_left _ _
  have h1 := hk D hD2
  rw [show (11 / 12 + 5 * (1 / 10) / 12 + 1 / 48 : ℝ) = 47 / 48 by norm_num] at h1
  unfold A1sum at h1
  rw [hA D hD2 _ _ (by linarith)] at h1
  have hD0 : 0 < D := by linarith
  -- D = D^(47/48) * D^(1/48)
  have hsplit : D = D ^ (47 / 48 : ℝ) * D ^ (1 / 48 : ℝ) := by
    rw [← Real.rpow_add hD0]; norm_num
  have hpos : 0 < D ^ (47 / 48 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hbig : |k| + 1 ≤ D ^ (1 / 48 : ℝ) := by
    have hk1 : (0:ℝ) ≤ |k| + 1 := by positivity
    have : (|k| + 1) ^ (48 : ℕ) ≤ D := le_max_right _ _
    calc |k| + 1 = ((|k| + 1) ^ (48 : ℕ)) ^ (1 / 48 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hk1]; norm_num
      _ ≤ D ^ (1 / 48 : ℝ) := Real.rpow_le_rpow (by positivity) this (by norm_num)
  have : D ^ (47 / 48 : ℝ) * (|k| + 1) ≤ k * D ^ (47 / 48 : ℝ) := by
    calc D ^ (47 / 48 : ℝ) * (|k| + 1) ≤ D ^ (47 / 48 : ℝ) * D ^ (1 / 48 : ℝ) :=
          mul_le_mul_of_nonneg_left hbig hpos.le
      _ = D := hsplit.symm
      _ ≤ _ := h1
  have := le_abs_self k
  nlinarith

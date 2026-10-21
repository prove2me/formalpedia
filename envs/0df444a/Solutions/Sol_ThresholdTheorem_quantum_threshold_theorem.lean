-- Prove2me | solution 1 for ThresholdTheorem.quantum_threshold_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-20T16:25:03.128704+00:00
-- url     : https://prove2.me/submissions/5f72267e-2671-4a5d-8cc6-588e3f828543
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model
import Theorems.Thm_ThresholdTheorem_level_k_concatenated_simulation
import Theorems.Thm_ThresholdTheorem_polylog_overhead_levels

open ThresholdTheorem

private lemma Operation.arity_le_two (o : Operation) : o.arity ≤ 2 := by
  cases o with
  | gate g => cases g <;> simp [Operation.arity, Gate.arity]
  | prep => simp [Operation.arity]
  | wait => simp [Operation.arity]

private lemma Operation.one_le_arity (o : Operation) : 1 ≤ o.arity := by
  cases o with
  | gate g => cases g <;> simp [Operation.arity, Gate.arity]
  | prep => simp [Operation.arity]
  | wait => simp [Operation.arity]

private lemma Layer.loc_length_bounds {n : ℕ} (L : Layer (Fin n)) :
    L.locs.length ≤ n ∧ n ≤ 2 * L.locs.length := by
  let l := L.locs.flatMap fun ℓ => List.ofFn ℓ.support
  have hlen : l.length = (L.locs.map fun ℓ => ℓ.op.arity).sum := by
    simp [l, List.length_flatMap]
  have hcount : ∀ q : Fin n, l.count q = 1 := by
    intro q
    simpa [l] using L.partition q
  have hto : l.toFinset = Finset.univ := by
    ext q
    rw [List.mem_toFinset]
    constructor
    · intro _; exact Finset.mem_univ q
    · intro _
      have hc : 0 < l.count q := by rw [hcount q]; norm_num
      exact List.count_pos_iff.mp hc
  have hsum : (∑ q : Fin n, l.count q) = l.length := by
    calc
      (∑ q : Fin n, l.count q) = ∑ q ∈ l.toFinset, l.count q := by rw [hto]
      _ = l.length := List.sum_toFinset_count_eq_length l
  have hsum_arities : (L.locs.map fun ℓ => ℓ.op.arity).sum = n := by
    rw [← hlen, ← hsum]
    simp [hcount]
  constructor
  · have hge : (L.locs.map fun _ => 1).sum ≤ (L.locs.map fun ℓ => ℓ.op.arity).sum := by
      apply List.sum_le_sum
      intro ℓ hℓ
      exact Operation.one_le_arity ℓ.op
    simpa [hsum_arities] using hge
  · have hle : (L.locs.map fun ℓ => ℓ.op.arity).sum ≤ (L.locs.map fun _ => 2).sum := by
      apply List.sum_le_sum
      intro ℓ hℓ
      exact Operation.arity_le_two ℓ.op
    have : n ≤ 2 * L.locs.length := by
      calc
        n = (L.locs.map fun ℓ => ℓ.op.arity).sum := hsum_arities.symm
        _ ≤ (L.locs.map fun _ => 2).sum := hle
        _ = 2 * L.locs.length := by simp [Nat.mul_comm]
    exact this

private lemma Circuit.size_bounds {n D : ℕ} (C : Circuit (Fin n)) (hD : C.length = D) :
    C.size ≤ n * D ∧ n * D ≤ 2 * C.size := by
  induction C generalizing D with
  | nil =>
      simp [Circuit.size] at hD ⊢
      omega
  | cons L Ls ih =>
      have hlen : Ls.length + 1 = D := by simpa using hD
      have hD' : Ls.length = D - 1 := by omega
      have hDpos : 0 < D := by omega
      have hDsucc : D = (D - 1) + 1 := by omega
      have hL := Layer.loc_length_bounds L
      have hLs := ih hD'
      simp only [Circuit.size, List.map_cons, List.sum_cons, List.length_cons] at *
      constructor
      · rw [hDsucc]
        nlinarith [hL.1, hLs.1]
      · rw [hDsucc]
        nlinarith [hL.2, hLs.2]

private lemma log_base_nonneg {m : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 ≤ Real.log ((m : ℝ) / ε) + 1 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hdiv : (1 : ℝ) < (m : ℝ) / ε := by
      rw [lt_div_iff₀ hε0]
      nlinarith
    have hlog : 0 ≤ Real.log ((m : ℝ) / ε) := Real.log_nonneg hdiv.le
    linarith

private lemma log_base_le_four_mul {m x : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hm : 0 < m) (hx : 0 < x) (hle : (m : ℝ) ≤ 2 * (x : ℝ)) :
    Real.log ((m : ℝ) / ε) + 1 ≤ 4 * (Real.log ((x : ℝ) / ε) + 1) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hx)
  have hdivx : (1 : ℝ) < (x : ℝ) / ε := by
    rw [lt_div_iff₀ hε0]
    nlinarith
  have hlogx_pos : 0 < Real.log ((x : ℝ) / ε) := Real.log_pos hdivx
  have hmpos : (0 : ℝ) < (m : ℝ) / ε := by
    have hmpos' : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hle_div : (m : ℝ) / ε ≤ (2 * (x : ℝ)) / ε := by
    exact div_le_div_of_nonneg_right hle hε0.le
  have hlog_le : Real.log ((m : ℝ) / ε) ≤ Real.log ((2 * (x : ℝ)) / ε) :=
    Real.log_le_log hmpos hle_div
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  calc
    Real.log ((m : ℝ) / ε) + 1 ≤ Real.log ((2 * (x : ℝ)) / ε) + 1 := by linarith
    _ = Real.log 2 + Real.log ((x : ℝ) / ε) + 1 := by
      rw [show (2 * (x : ℝ)) / ε = 2 * ((x : ℝ) / ε) by ring]
      rw [Real.log_mul (by norm_num) (by positivity)]
    _ ≤ 4 * (Real.log ((x : ℝ) / ε) + 1) := by nlinarith

theorem solution :
    ∃ pth : ℝ, 0 < pth ∧ ∃ c : ℕ, ∀ p : ℝ, 0 ≤ p → p < pth → ∃ A : ℝ,
      ∀ (n D : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
          ∀ C : Circuit (Fin n), C.length = D →
            ∃ C' : Circuit (Fin n × Fin b),
              (C'.size : ℝ) ≤ A * (Real.log (C.size / ε) + 1) ^ c * C.size ∧
              ∀ N : NoiseModel p,
                tvDist (decodeDist dec (outDist (noisyState N C'))) (outDist (idealState C))
                  ≤ ε := by
  rcases ThresholdTheorem.level_k_concatenated_simulation with ⟨c, A0, d, hc, hlev⟩
  refine ⟨min 1 (1 / c), ?_, Nat.clog 2 d, ?_⟩
  · exact lt_min one_pos (one_div_pos.mpr hc)
  · intro p hp hp_lt
    have hp_lt_div : p < 1 / c := lt_of_lt_of_le hp_lt (min_le_right _ _)
    have hcp : c * p < 1 := by
      have h := mul_lt_mul_of_pos_left hp_lt_div hc
      rwa [mul_one_div_cancel hc.ne'] at h
    rcases ThresholdTheorem.polylog_overhead_levels c p d hc hp hcp with ⟨A1, hpoly⟩
    let r : ℕ := Nat.clog 2 d
    let A : ℝ := max A0 0 * (max A1 0 * 4 ^ r)
    refine ⟨A, ?_⟩
    intro n D ε hε0 hε1
    let g : ℕ := max (n * D) 1
    have hg : 1 ≤ g := le_max_right _ _
    rcases hpoly g ε hg hε0 hε1 with ⟨k, herr, hsize⟩
    rcases hlev k with ⟨b, dec, hlevk⟩
    refine ⟨b, dec, ?_⟩
    intro C hC
    have hbounds := Circuit.size_bounds C hC
    rcases hlevk n C with ⟨C', hC'_size, hC'_err⟩
    refine ⟨C', ?_, ?_⟩
    · by_cases hnD : n * D = 0
      · have hCsize0 : C.size = 0 := by
          have := hbounds.1
          omega
        have hC'0 : C'.size = 0 := by
          have hnonneg : (0 : ℝ) ≤ (C'.size : ℝ) := by exact_mod_cast Nat.zero_le C'.size
          have hle0 : (C'.size : ℝ) ≤ 0 := by
            simpa [hCsize0] using hC'_size
          have hle0' : C'.size ≤ 0 := by exact_mod_cast hle0
          omega
        simp [hCsize0, hC'0]
      · have hnDpos : 0 < n * D := Nat.pos_of_ne_zero hnD
        have hCpos : 0 < C.size := by
          have h2 := hbounds.2
          omega
        have hg_eq : g = n * D := by
          dsimp [g]
          exact max_eq_left (Nat.one_le_iff_ne_zero.mpr hnD)
        have hsize' : (d : ℝ) ^ k ≤ A1 * (Real.log (((n * D : ℕ) : ℝ) / ε) + 1) ^ r := by
          simpa [r, hg_eq] using hsize
        have hxle : (((n * D : ℕ) : ℝ)) ≤ 2 * (C.size : ℝ) := by
          exact_mod_cast hbounds.2
        have hbase_le : Real.log (((n * D : ℕ) : ℝ) / ε) + 1 ≤
            4 * (Real.log ((C.size : ℝ) / ε) + 1) :=
          log_base_le_four_mul (m := n * D) (x := C.size) hε0 hε1 hnDpos hCpos hxle
        have hbase_g_nonneg : 0 ≤ Real.log (((n * D : ℕ) : ℝ) / ε) + 1 :=
          log_base_nonneg (m := n * D) hε0 hε1
        have hbase_c_nonneg : 0 ≤ Real.log ((C.size : ℝ) / ε) + 1 :=
          log_base_nonneg (m := C.size) hε0 hε1
        have hpow_le : (Real.log (((n * D : ℕ) : ℝ) / ε) + 1) ^ r ≤
            (4 * (Real.log ((C.size : ℝ) / ε) + 1)) ^ r :=
          pow_le_pow_left₀ hbase_g_nonneg hbase_le r
        have hsize_d : (d : ℝ) ^ k ≤
            (max A1 0 * 4 ^ r) * (Real.log ((C.size : ℝ) / ε) + 1) ^ r := by
          calc
            (d : ℝ) ^ k ≤ A1 * (Real.log (((n * D : ℕ) : ℝ) / ε) + 1) ^ r := hsize'
            _ ≤ max A1 0 * (Real.log (((n * D : ℕ) : ℝ) / ε) + 1) ^ r :=
              mul_le_mul_of_nonneg_right (le_max_left A1 0) (pow_nonneg hbase_g_nonneg r)
            _ ≤ max A1 0 * (4 * (Real.log ((C.size : ℝ) / ε) + 1)) ^ r :=
              mul_le_mul_of_nonneg_left hpow_le (le_max_right A1 0)
            _ = max A1 0 * (4 ^ r * (Real.log ((C.size : ℝ) / ε) + 1) ^ r) := by
              rw [mul_pow]
            _ = (max A1 0 * 4 ^ r) * (Real.log ((C.size : ℝ) / ε) + 1) ^ r := by ring
        have hsize0 : (C'.size : ℝ) ≤ max A0 0 * (d : ℝ) ^ k * (C.size : ℝ) := by
          have hcoef : 0 ≤ (d : ℝ) ^ k * (C.size : ℝ) :=
            mul_nonneg (pow_nonneg (Nat.cast_nonneg d) k) (by exact_mod_cast Nat.zero_le C.size)
          calc
            (C'.size : ℝ) ≤ A0 * (d : ℝ) ^ k * C.size := hC'_size
            _ = A0 * ((d : ℝ) ^ k * (C.size : ℝ)) := by ring
            _ ≤ max A0 0 * ((d : ℝ) ^ k * (C.size : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left A0 0) hcoef
            _ = max A0 0 * (d : ℝ) ^ k * (C.size : ℝ) := by ring
        have hA0nonneg : 0 ≤ max A0 0 := le_max_right _ _
        have hCnonneg : 0 ≤ (C.size : ℝ) := by exact_mod_cast Nat.zero_le C.size
        have hmul := mul_le_mul_of_nonneg_left hsize_d (mul_nonneg hA0nonneg hCnonneg)
        have hfinal : (C'.size : ℝ) ≤
            A * (Real.log ((C.size : ℝ) / ε) + 1) ^ r * (C.size : ℝ) := by
          calc
            (C'.size : ℝ) ≤ max A0 0 * (d : ℝ) ^ k * (C.size : ℝ) := hsize0
            _ = (max A0 0 * (C.size : ℝ)) * (d : ℝ) ^ k := by ring
            _ ≤ (max A0 0 * (C.size : ℝ)) *
                ((max A1 0 * 4 ^ r) * (Real.log ((C.size : ℝ) / ε) + 1) ^ r) := hmul
            _ = A * (Real.log ((C.size : ℝ) / ε) + 1) ^ r * (C.size : ℝ) := by
              dsimp [A]
              ring
        simpa [r] using hfinal
    · intro N
      have hC_le_g : (C.size : ℝ) ≤ (g : ℝ) := by
        have hnat : C.size ≤ g := le_trans hbounds.1 (le_max_left _ _)
        exact_mod_cast hnat
      have hfactor_nonneg : 0 ≤ (c * p) ^ (2 ^ k) / c :=
        div_nonneg (pow_nonneg (mul_nonneg hc.le hp) _) hc.le
      calc
        tvDist (decodeDist dec (outDist (noisyState N C'))) (outDist (idealState C))
            ≤ (c * p) ^ (2 ^ k) / c * (C.size : ℝ) := hC'_err p hp hcp N
        _ ≤ (c * p) ^ (2 ^ k) / c * (g : ℝ) :=
          mul_le_mul_of_nonneg_left hC_le_g hfactor_nonneg
        _ = (g : ℝ) * ((c * p) ^ (2 ^ k) / c) := by ring
        _ ≤ ε := herr

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P48.beam_splitter_ordering
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:44:51.105023+00:00
-- url     : https://prove2.me/submissions/13cc1174-356c-4712-9b4e-23b49de0a253

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P48


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P48

open Filter

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ}

lemma x5pb_filter_succ (j : ℕ) (hj : j < m + 1) :
    (Finset.univ.filter (fun k : Fin (m + 1) => k.val < j + 1)) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun k : Fin (m + 1) => k.val < j)) := by
  ext k; simp [Fin.ext_iff]; omega

lemma x5pb_E_succ (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ) (j : ℕ)
    (hj : j < m + 1) :
    emittedPhotons order out (j + 1) = emittedPhotons order out j + out (order ⟨j, hj⟩) := by
  unfold emittedPhotons
  rw [x5pb_filter_succ j hj, Finset.sum_insert (by simp)]
  ring

lemma x5pb_R_succ (eta : Fin (m + 1) → ℝ≥0) (order : Equiv.Perm (Fin (m + 1))) (j : ℕ)
    (hj : j < m + 1) :
    residualIntensity eta order (j + 1) = residualIntensity eta order j - eta (order ⟨j, hj⟩) := by
  unfold residualIntensity
  rw [x5pb_filter_succ j hj, Finset.sum_insert (by simp)]
  ring

lemma x5pb_filter_full :
    (Finset.univ.filter (fun k : Fin (m + 1) => k.val < m + 1)) = Finset.univ := by
  ext k; simp; omega

lemma x5pb_E_full (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ) :
    emittedPhotons order out (m + 1) = ∑ i, out i := by
  unfold emittedPhotons
  rw [x5pb_filter_full]
  exact Equiv.sum_comp order out

lemma x5pb_R_full (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (order : Equiv.Perm (Fin (m + 1))) : residualIntensity eta order (m + 1) = 0 := by
  unfold residualIntensity
  rw [x5pb_filter_full, Equiv.sum_comp order (fun i => (eta i : ℝ))]
  have : (∑ i, (eta i : ℝ)) = 1 := by exact_mod_cast heta
  linarith

lemma x5pb_R_zero (eta : Fin (m + 1) → ℝ≥0) (order : Equiv.Perm (Fin (m + 1))) :
    residualIntensity eta order 0 = 1 := by
  simp [residualIntensity]

lemma x5pb_R_nonneg (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (order : Equiv.Perm (Fin (m + 1))) (j : ℕ) : 0 ≤ residualIntensity eta order j := by
  unfold residualIntensity
  have h1 : (∑ i, (eta (order i) : ℝ)) = 1 := by
    rw [Equiv.sum_comp order (fun i => (eta i : ℝ))]; exact_mod_cast heta
  have h2 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (m + 1)))
    (fun k : Fin (m + 1) => k.val < j) (fun i => (eta (order i) : ℝ))
  have h3 : 0 ≤ ∑ x ∈ Finset.univ.filter (fun k : Fin (m + 1) => ¬ k.val < j), (eta (order x) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)
  linarith

lemma x5pb_E_le (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ) (j : ℕ) :
    emittedPhotons order out j ≤ ∑ i, out i := by
  rw [← x5pb_E_full order out]
  unfold emittedPhotons
  rw [x5pb_filter_full]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- the splitter parameters -/
def x5pbT (eta : Fin (m + 1) → ℝ≥0) (order : Equiv.Perm (Fin (m + 1))) (j : Fin m) : ℝ :=
  if 0 < residualIntensity eta order j.val then
    residualIntensity eta order (j.val + 1) / residualIntensity eta order j.val else 0

lemma x5pb_T_bounds (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (order : Equiv.Perm (Fin (m + 1))) (j : Fin m) :
    0 ≤ x5pbT eta order j ∧ x5pbT eta order j ≤ 1 := by
  unfold x5pbT
  split_ifs with h
  · have h1 := x5pb_R_nonneg eta heta order (j.val + 1)
    have h2 := x5pb_R_succ eta order j.val (by omega)
    have h3 : (0 : ℝ) ≤ eta (order ⟨j.val, by omega⟩) := NNReal.coe_nonneg _
    refine ⟨div_nonneg h1 h.le, (div_le_one h).2 (by linarith)⟩
  · exact ⟨le_refl _, zero_le_one⟩

/-- the squared stage factor -/
def x5pbF (eta : Fin (m + 1) → ℝ≥0) (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ)
    (n : ℕ) (j : Fin m) : ℝ :=
  (Nat.choose (n - emittedPhotons order out j.val) (out (order j.castSucc)) : ℝ) *
    (1 - x5pbT eta order j) ^ out (order j.castSucc) *
    x5pbT eta order j ^ (n - emittedPhotons order out j.val - out (order j.castSucc))

lemma x5pb_key (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ) (j : Fin m) :
    let n := ∑ i, out i
    x5pbF eta order out n j * residualIntensity eta order j.val ^ (n - emittedPhotons order out j.val) =
      (Nat.choose (n - emittedPhotons order out j.val) (out (order j.castSucc)) : ℝ) *
        (eta (order j.castSucc) : ℝ) ^ out (order j.castSucc) *
        residualIntensity eta order (j.val + 1) ^ (n - emittedPhotons order out (j.val + 1)) := by
  intro n
  unfold x5pbF x5pbT
  have hE := x5pb_E_succ order out j.val (by omega)
  have hle := x5pb_E_le order out (j.val + 1)
  have hcs : (⟨j.val, by omega⟩ : Fin (m + 1)) = j.castSucc := rfl
  rw [hcs] at hE
  have hR := x5pb_R_succ eta order j.val (by omega)
  rw [hcs] at hR
  set o := out (order j.castSucc)
  set E := emittedPhotons order out j.val
  set k := n - emittedPhotons order out (j.val + 1)
  have hk : n - E - o = k := by simp only [k]; omega
  have hsplit : n - E = o + k := by simp only [k]; omega
  rw [hk, hsplit]
  set R := residualIntensity eta order j.val
  set R' := residualIntensity eta order (j.val + 1)
  set et := (eta (order j.castSucc) : ℝ)
  have hR'0 : 0 ≤ R' := x5pb_R_nonneg eta heta order _
  have het0 : 0 ≤ et := NNReal.coe_nonneg _
  have hR0 : 0 ≤ R := x5pb_R_nonneg eta heta order _
  by_cases hpos : 0 < R
  · rw [if_pos hpos]
    have h1 : 1 - R' / R = et / R := by field_simp; linarith
    rw [h1, pow_add, div_pow, div_pow]
    field_simp
  · rw [if_neg hpos]
    have hR00 : R = 0 := le_antisymm (not_lt.1 hpos) hR0
    have hR'00 : R' = 0 := by linarith
    have het00 : et = 0 := by linarith
    rw [hR00, hR'00, het00]
    rcases Nat.eq_zero_or_pos o with ho | ho
    · rcases Nat.eq_zero_or_pos k with hk' | hk'
      · simp [ho, hk']
      · simp [ho, zero_pow hk'.ne']
    · simp [zero_pow ho.ne', zero_pow (by omega : o + k ≠ 0)]

end QAlgorithms.Papers.Independent.Support50.P48


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P48

open Filter

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ}

lemma x5pb_filterM_succ (j : ℕ) (hj : j < m) :
    (Finset.univ.filter (fun k : Fin m => k.val < j + 1)) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun k : Fin m => k.val < j)) := by
  ext k; simp [Fin.ext_iff]; omega

lemma x5pb_ind (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ) (j : ℕ) (hj : j ≤ m) :
    ∏ i ∈ Finset.univ.filter (fun k : Fin m => k.val < j), x5pbF eta order out (∑ i, out i) i =
      (∏ i ∈ Finset.univ.filter (fun k : Fin m => k.val < j),
        (Nat.choose ((∑ i, out i) - emittedPhotons order out i.val) (out (order i.castSucc)) : ℝ) *
        (eta (order i.castSucc) : ℝ) ^ out (order i.castSucc)) *
      residualIntensity eta order j ^ ((∑ i, out i) - emittedPhotons order out j) := by
  induction j with
  | zero => simp [x5pb_R_zero, emittedPhotons]
  | succ j ih =>
    rw [x5pb_filterM_succ j (by omega), Finset.prod_insert (by simp),
      Finset.prod_insert (by simp), ih (by omega)]
    have := x5pb_key eta heta order out ⟨j, by omega⟩
    simp only at this
    rw [mul_comm (x5pbF _ _ _ _ _), mul_assoc, mul_comm (residualIntensity _ _ _ ^ _), this]
    ring

lemma x5pb_multi (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ) (j : ℕ) (hj : j ≤ m) :
    (∏ i ∈ Finset.univ.filter (fun k : Fin m => k.val < j),
        Nat.choose ((∑ i, out i) - emittedPhotons order out i.val) (out (order i.castSucc))) *
      (∏ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => k.val < j), (out (order k)).factorial) *
      ((∑ i, out i) - emittedPhotons order out j).factorial = (∑ i, out i).factorial := by
  induction j with
  | zero => simp [emittedPhotons]
  | succ j ih =>
    rw [x5pb_filterM_succ j (by omega), Finset.prod_insert (by simp),
      x5pb_filter_succ j (by omega), Finset.prod_insert (by simp)]
    have hE := x5pb_E_succ order out j (by omega)
    have hle := x5pb_E_le order out (j + 1)
    have hcs : (⟨j, by omega⟩ : Fin (m + 1)) = (⟨j, by omega⟩ : Fin m).castSucc := rfl
    rw [← hcs]
    have hc := Nat.choose_mul_factorial_mul_factorial
      (n := (∑ i, out i) - emittedPhotons order out j) (k := out (order ⟨j, by omega⟩)) (by omega)
    rw [show (∑ i, out i) - emittedPhotons order out j - out (order ⟨j, by omega⟩) =
      (∑ i, out i) - emittedPhotons order out (j + 1) by omega] at hc
    rw [← ih (by omega), ← hc]
    simp only [Fin.castSucc_mk]
    ring

lemma x5pb_filter_m_prod {β : Type*} [CommMonoid β] (f : Fin (m + 1) → β) :
    ∏ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => k.val < m), f k = ∏ i : Fin m, f i.castSucc := by
  rw [show Finset.univ.filter (fun k : Fin (m + 1) => k.val < m) =
    Finset.univ.image Fin.castSucc by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨⟨k.val, h⟩, rfl⟩
      · rintro ⟨i, rfl⟩; simp]
  rw [Finset.prod_image (fun a _ b _ h => Fin.castSucc_injective m h)]

lemma x5pb_filterM_full :
    (Finset.univ.filter (fun k : Fin m => k.val < m)) = Finset.univ := by
  ext k; simp

lemma x5pb_sq_sqrt_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : (Real.sqrt x ^ k) ^ 2 = x ^ k := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]

theorem x5pb_amp (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ) (n : ℕ) :
    sequentialAmplitude (x5pbT eta order) order out n = vacuumAmplitude eta out n := by
  unfold sequentialAmplitude vacuumAmplitude
  by_cases hn : (∑ i, out i) = n
  swap
  · rw [if_neg hn, if_neg hn]
  rw [if_pos hn, if_pos hn]
  subst hn
  set n := ∑ i, out i
  have hT := x5pb_T_bounds eta heta order
  have h1 : 0 ≤ ∏ j : Fin m,
      Real.sqrt (Nat.choose (n - emittedPhotons order out j.val) (out (order j.castSucc)) : ℝ) *
      Real.sqrt (1 - x5pbT eta order j) ^ out (order j.castSucc) *
      Real.sqrt (x5pbT eta order j) ^ (n - emittedPhotons order out j.val - out (order j.castSucc)) :=
    Finset.prod_nonneg (fun j _ => by positivity)
  have h2 : 0 ≤ Real.sqrt ((Nat.factorial n : ℝ) / ∏ i, (Nat.factorial (out i) : ℝ)) *
      ∏ i, Real.sqrt (eta i : ℝ) ^ out i := by positivity
  refine (sq_eq_sq₀ h1 h2).1 ?_
  rw [← Finset.prod_pow, mul_pow, ← Finset.prod_pow, Real.sq_sqrt (by positivity)]
  have hL : ∀ j : Fin m, (Real.sqrt (Nat.choose (n - emittedPhotons order out j.val)
      (out (order j.castSucc)) : ℝ) *
      Real.sqrt (1 - x5pbT eta order j) ^ out (order j.castSucc) *
      Real.sqrt (x5pbT eta order j) ^ (n - emittedPhotons order out j.val - out (order j.castSucc))) ^ 2
      = x5pbF eta order out n j := by
    intro j
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      x5pb_sq_sqrt_pow _ (by linarith [(hT j).2]), x5pb_sq_sqrt_pow _ (hT j).1]
    rfl
  simp_rw [hL]
  simp_rw [x5pb_sq_sqrt_pow _ (NNReal.coe_nonneg _)]
  have hI := x5pb_ind eta heta order out m le_rfl
  simp only [x5pb_filterM_full] at hI
  rw [hI, Finset.prod_mul_distrib]
  -- residual at m and remaining photons
  have hRm : residualIntensity eta order m = eta (order (Fin.last m)) := by
    have := x5pb_R_succ eta order m (by omega)
    rw [x5pb_R_full eta heta order] at this
    have hl : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    rw [hl] at this; linarith
  have hEm : n - emittedPhotons order out m = out (order (Fin.last m)) := by
    have := x5pb_E_succ order out m (by omega)
    rw [x5pb_E_full] at this
    have hl : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    rw [hl] at this; simp only [n]; omega
  rw [hRm, hEm]
  -- multinomial coefficient
  have hM := x5pb_multi order out m le_rfl
  simp only [x5pb_filterM_full] at hM
  rw [x5pb_filter_m_prod, hEm] at hM
  have hFp : (∏ i, (Nat.factorial (out i) : ℝ)) =
      (∏ i : Fin m, ((out (order i.castSucc)).factorial : ℝ)) * (out (order (Fin.last m))).factorial := by
    rw [← Equiv.prod_comp order (fun i => (Nat.factorial (out i) : ℝ)), Fin.prod_univ_castSucc]
  have hEp : (∏ i, (eta i : ℝ) ^ out i) =
      (∏ i : Fin m, (eta (order i.castSucc) : ℝ) ^ out (order i.castSucc)) *
        (eta (order (Fin.last m)) : ℝ) ^ out (order (Fin.last m)) := by
    rw [← Equiv.prod_comp order (fun i => (eta i : ℝ) ^ out i), Fin.prod_univ_castSucc]
  rw [hFp, hEp]
  have hMr : ((∏ i : Fin m, Nat.choose (n - emittedPhotons order out i.val) (out (order i.castSucc)) : ℕ) : ℝ) *
      ((∏ i : Fin m, ((out (order i.castSucc)).factorial : ℝ)) *
        (out (order (Fin.last m))).factorial) = (n.factorial : ℝ) := by
    rw [← mul_assoc]; exact_mod_cast hM
  have hpos : (0 : ℝ) < (∏ i : Fin m, ((out (order i.castSucc)).factorial : ℝ)) *
      (out (order (Fin.last m))).factorial := by positivity
  rw [← hMr]
  push_cast
  field_simp
  ring

end QAlgorithms.Papers.Independent.Support50.P48


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P48

open Filter

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ}

/-- the vacuum amplitude at its own photon number -/
def x5pbA (eta : Fin (m + 1) → ℝ≥0) (o : Fin (m + 1) → ℕ) : ℝ := vacuumAmplitude eta o (∑ i, o i)

lemma x5pb_A_sq (eta : Fin (m + 1) → ℝ≥0) (o : Fin (m + 1) → ℕ) :
    x5pbA eta o ^ 2 = (Nat.multinomial Finset.univ o : ℝ) * ∏ i, (eta i : ℝ) ^ o i := by
  unfold x5pbA vacuumAmplitude
  rw [if_pos rfl, mul_pow, Real.sq_sqrt (by positivity), ← Finset.prod_pow]
  simp_rw [x5pb_sq_sqrt_pow _ (NNReal.coe_nonneg _)]
  congr 1
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin (m + 1))) o
  have hpos : (0 : ℝ) < ∏ i, ((o i).factorial : ℝ) := by positivity
  rw [div_eq_iff hpos.ne']
  have h' : ((∏ i, (o i).factorial : ℕ) : ℝ) * (Nat.multinomial Finset.univ o : ℝ) =
      ((∑ i, o i).factorial : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

lemma x5pb_A_sum (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1) (n : ℕ) :
    ∑ o ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (m + 1))) n, x5pbA eta o ^ 2 = 1 := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin (m + 1)))
    (fun i => (eta i : ℝ)) n
  have h1 : (∑ i, (eta i : ℝ)) = 1 := by exact_mod_cast heta
  rw [h1, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  rw [x5pb_A_sq]

/-- the photon-number map -/
def x5pbPhi {R : Type} (a : R × (Fin (m + 1) → ℕ)) : R × ℕ := (a.1, ∑ i, a.2 i)

lemma x5pb_fiber (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1) {R : Type} (p : R × ℕ) :
    ∑' b : (x5pbPhi (m := m) (R := R)) ⁻¹' {p}, ENNReal.ofReal (x5pbA eta b.1.2 ^ 2) = 1 := by
  let e : (x5pbPhi (m := m) (R := R)) ⁻¹' {p} ≃
      ((Finset.piAntidiag (Finset.univ : Finset (Fin (m + 1))) p.2 : Finset _) : Set _) :=
    { toFun := fun b => ⟨b.1.2, by
        have := b.2; simp only [Set.mem_preimage, Set.mem_singleton_iff, x5pbPhi] at this
        simp [← this]⟩
      invFun := fun o => ⟨(p.1, o.1), by
        have := o.2; simp only [Finset.mem_coe, Finset.mem_piAntidiag] at this
        simp only [Set.mem_preimage, Set.mem_singleton_iff, x5pbPhi]
        ext <;> simp [this.1]⟩
      left_inv := fun b => by
        have := b.2; simp only [Set.mem_preimage, Set.mem_singleton_iff, x5pbPhi] at this
        apply Subtype.ext; simp [← this]
      right_inv := fun o => rfl }
  rw [← e.symm.tsum_eq]
  simp only [e, Equiv.coe_fn_symm_mk]
  rw [Finset.tsum_subtype' (Finset.piAntidiag (Finset.univ : Finset (Fin (m + 1))) p.2)
    (fun o => ENNReal.ofReal (x5pbA eta o ^ 2))]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), x5pb_A_sum eta heta,
    ENNReal.ofReal_one]

lemma x5pb_gl (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1) {R : Type}
    (h : R × ℕ → ℝ≥0∞) :
    ∑' a : R × (Fin (m + 1) → ℕ), ENNReal.ofReal (x5pbA eta a.2 ^ 2) * h (x5pbPhi a) =
      ∑' p, h p := by
  rw [← ENNReal.tsum_fiberwise _ x5pbPhi]
  refine tsum_congr (fun p => ?_)
  have : ∀ b : (x5pbPhi (m := m) (R := R)) ⁻¹' {p},
      ENNReal.ofReal (x5pbA eta b.1.2 ^ 2) * h (x5pbPhi b.1) =
        ENNReal.ofReal (x5pbA eta b.1.2 ^ 2) * h p := by
    intro b; rw [show x5pbPhi b.1 = p from b.2]
  rw [tsum_congr this, ENNReal.tsum_mul_right, x5pb_fiber eta heta, one_mul]

/-- real-valued version for nonnegative summable functions -/
lemma x5pb_gl_real (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1) {R : Type}
    (h : R × ℕ → ℝ) (h0 : ∀ p, 0 ≤ h p) (hs : Summable h) :
    HasSum (fun a : R × (Fin (m + 1) → ℕ) => x5pbA eta a.2 ^ 2 * h (x5pbPhi a)) (∑' p, h p) := by
  set g : R × (Fin (m + 1) → ℕ) → ℝ≥0 := fun a => (x5pbA eta a.2 ^ 2 * h (x5pbPhi a)).toNNReal
  set h' : R × ℕ → ℝ≥0 := fun p => (h p).toNNReal
  have hs' : Summable h' := hs.toNNReal
  have hE : ∑' a, (g a : ℝ≥0∞) = ∑' p, (h' p : ℝ≥0∞) := by
    have := x5pb_gl eta heta (fun p => ENNReal.ofReal (h p))
    show ∑' a, ENNReal.ofReal (x5pbA eta a.2 ^ 2 * h (x5pbPhi a)) = ∑' p, ENNReal.ofReal (h p)
    rw [← this]
    refine tsum_congr (fun a => ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
  rw [ENNReal.tsum_coe_eq hs'.hasSum] at hE
  have hgs : Summable g := ENNReal.tsum_coe_ne_top_iff_summable.1 (by rw [hE]; simp)
  have hval : ∑' a, g a = ∑' p, h' p := by
    rw [← ENNReal.coe_inj, ENNReal.coe_tsum hgs, hE]
  have := (NNReal.hasSum_coe.2 hgs.hasSum)
  rw [hval, NNReal.coe_tsum] at this
  simp only [g, h', Real.coe_toNNReal _ (h0 _),
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) (h0 _))] at this
  exact this

end QAlgorithms.Papers.Independent.Support50.P48


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P48

open Filter

open scoped BigOperators ENNReal NNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.RealRegisters (Hilbert)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ}

lemma x5pb_hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num

lemma x5pb_normsq {R : Type} (eta : Fin (m + 1) → ℝ≥0) (u : Hilbert (R × ℕ))
    (a : R × (Fin (m + 1) → ℕ)) :
    ‖(x5pbA eta a.2 : ℂ) * u (x5pbPhi a)‖ ^ (2 : ℝ≥0∞).toReal =
      x5pbA eta a.2 ^ 2 * ‖u (x5pbPhi a)‖ ^ (2 : ℝ≥0∞).toReal := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, show (2 : ℝ≥0∞).toReal = 2 by norm_num,
    Real.mul_rpow (abs_nonneg _) (norm_nonneg _), Real.rpow_two, sq_abs]

lemma x5pb_V_hasSum {R : Type} (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (u : Hilbert (R × ℕ)) :
    HasSum (fun a : R × (Fin (m + 1) → ℕ) =>
      ‖(x5pbA eta a.2 : ℂ) * u (x5pbPhi a)‖ ^ (2 : ℝ≥0∞).toReal)
      (∑' p, ‖u p‖ ^ (2 : ℝ≥0∞).toReal) := by
  simp_rw [x5pb_normsq]
  exact x5pb_gl_real eta heta (fun p => ‖u p‖ ^ (2 : ℝ≥0∞).toReal)
    (fun p => by positivity) ((memℓp_gen_iff x5pb_hp).1 (lp.memℓp u))

/-- the vacuum isometry -/
def x5pbV {R : Type} (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1) (u : Hilbert (R × ℕ)) :
    Hilbert (R × (Fin (m + 1) → ℕ)) :=
  ⟨fun a => (x5pbA eta a.2 : ℂ) * u (x5pbPhi a),
    (memℓp_gen_iff x5pb_hp).2 (x5pb_V_hasSum eta heta u).summable⟩

lemma x5pb_V_apply {R : Type} (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (u : Hilbert (R × ℕ)) (a : R × (Fin (m + 1) → ℕ)) :
    x5pbV eta heta u a = (x5pbA eta a.2 : ℂ) * u (x5pbPhi a) := rfl

lemma x5pb_V_norm {R : Type} (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (u : Hilbert (R × ℕ)) : ‖x5pbV eta heta u‖ = ‖u‖ := by
  rw [lp.norm_eq_tsum_rpow x5pb_hp, lp.norm_eq_tsum_rpow x5pb_hp]
  congr 1
  exact (x5pb_V_hasSum eta heta u).tsum_eq

lemma x5pb_diag_nonneg {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (p : I) :
    0 ≤ (X p p).re := by
  have := (hX.2.1 {p} (fun _ => 1)).2
  simpa using this

theorem x5pb_density {R : Type} (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (X : Matrix (R × ℕ) (R × ℕ) ℂ) (hX : IsDensity X) :
    IsDensity (referencedVacuumOutput (vacuumAmplitude eta) X) := by
  have hY : ∀ a b, referencedVacuumOutput (vacuumAmplitude eta) X a b =
      (x5pbA eta a.2 : ℂ) * X (x5pbPhi a) (x5pbPhi b) * (x5pbA eta b.2 : ℂ) := fun a b => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- trace class
    obtain ⟨e⟩ := hX.1
    refine ⟨{ left := fun n => x5pbV eta heta (e.left n)
              right := fun n => x5pbV eta heta (e.right n)
              summable := ?_
              coefficients := ?_ }⟩
    · simp_rw [x5pb_V_norm]; exact e.summable
    · intro a b
      rw [hY, e.coefficients]
      simp_rw [x5pb_V_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
      rw [← tsum_mul_left, ← tsum_mul_right]
      refine tsum_congr (fun n => ?_)
      ring
  · -- positivity
    intro s z
    set t := s.image (x5pbPhi (m := m) (R := R))
    set w : R × ℕ → ℂ := fun p =>
      ∑ a ∈ s.filter (fun a => x5pbPhi a = p), (x5pbA eta a.2 : ℂ) * z a
    have hmaps : ∀ a ∈ s, x5pbPhi a ∈ t := fun a ha => Finset.mem_image_of_mem _ ha
    have hQ : (∑ i ∈ s, ∑ j ∈ s, star (z i) * referencedVacuumOutput (vacuumAmplitude eta) X i j * z j) =
        ∑ p ∈ t, ∑ q ∈ t, star (w p) * X p q * w q := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp_rw [← Finset.sum_fiberwise_of_maps_to hmaps (f := fun j =>
        star (z _) * referencedVacuumOutput (vacuumAmplitude eta) X _ j * z j)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [w, star_sum, Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
      rw [(Finset.mem_filter.1 hi).2.symm, (Finset.mem_filter.1 hj).2.symm, hY]
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    rw [hQ]
    exact hX.2.1 t w
  · -- summable diagonal
    have := x5pb_gl_real eta heta (fun p => (X p p).re) (x5pb_diag_nonneg hX) hX.2.2.1
    refine this.summable.congr (fun a => ?_)
    rw [hY]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · have := x5pb_gl_real eta heta (fun p => (X p p).re) (x5pb_diag_nonneg hX) hX.2.2.1
    rw [hX.2.2.2] at this
    rw [← this.tsum_eq]
    refine tsum_congr (fun a => ?_)
    rw [hY]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring

end QAlgorithms.Papers.Independent.Support50.P48


noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal Topology

open QAlgorithms.Papers.Independent.Support50.P48

open QAlgorithms.Papers.Independent.Dependency50.P30
  (PureLossBroadcastParameters thermalEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {m : ℕ} (hm : 0 < m)
    (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (order : Equiv.Perm (Fin (m + 1))) :
    ∃ t : Fin m → ℝ,
      (∀ j, 0 ≤ t j ∧ t j ≤ 1) ∧
      (∀ j, 0 < residualIntensity eta order j.val →
        t j = residualIntensity eta order (j.val + 1) /
          residualIntensity eta order j.val) ∧
      (∀ out n, sequentialAmplitude t order out n = vacuumAmplitude eta out n) ∧
      (∀ (R : Type) (rho : State (R × ℕ)),
        IsDensity (referencedVacuumOutput (sequentialAmplitude t order) rho.coefficients) ∧
        referencedVacuumOutput (sequentialAmplitude t order) rho.coefficients =
          referencedVacuumOutput (vacuumAmplitude eta) rho.coefficients) := by
  have hamp : sequentialAmplitude (x5pbT eta order) order = vacuumAmplitude eta := by
    funext out n; exact x5pb_amp eta heta order out n
  refine ⟨x5pbT eta order, x5pb_T_bounds eta heta order, fun j hj => ?_,
    fun out n => x5pb_amp eta heta order out n, fun R rho => ?_⟩
  · unfold x5pbT; rw [if_pos hj]
  · rw [hamp]
    exact ⟨x5pb_density eta heta rho.coefficients rho.density, rfl⟩


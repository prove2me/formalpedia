-- Prove2me | solution 1 for RamanujanLostNotebook.PartII.theorem_1_2_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:39:38.455523+00:00
-- url     : https://prove2.me/submissions/05209814-1ab5-4ca3-9749-dab4606d6f00

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

open Filter Topology

namespace S100R121

open RamanujanLostNotebook.PartII

lemma qPoch_succ (a q : ℂ) (n : ℕ) : qPoch a q (n + 1) = qPoch a q n * (1 - a * q ^ n) := by
  unfold qPoch; rw [Finset.prod_range_succ]

lemma qPoch_add (a q : ℂ) (n N : ℕ) :
    qPoch a q (n + N) = qPoch a q n * qPoch (a * q ^ n) q N := by
  unfold qPoch; rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [pow_add]; ring

lemma qPoch_ne_zero {a q : ℂ} (h : ∀ k : ℕ, a * q ^ k ≠ 1) (n : ℕ) : qPoch a q n ≠ 0 := by
  unfold qPoch
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => sub_ne_zero.mpr (h k).symm)

lemma norm_mul_pow_le {z q : ℂ} (hq : ‖q‖ ≤ 1) (k : ℕ) : ‖z * q ^ k‖ ≤ ‖z‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq)

lemma ne_one_of_norm {z q : ℂ} (hz : ‖z‖ < 1) (hq : ‖q‖ ≤ 1) (k : ℕ) : z * q ^ k ≠ 1 := by
  intro h
  have := norm_mul_pow_le (z := z) hq k
  rw [h, norm_one] at this
  linarith

lemma summable_norm_geom {a q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => ‖-(a * q ^ k)‖) := by
  simp only [norm_neg, norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left _

lemma hasProd_qPochInf {a q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun k : ℕ => 1 - a * q ^ k) (qPochInf a q) := by
  have hm : Multipliable (fun k : ℕ => 1 + -(a * q ^ k)) :=
    multipliable_one_add_of_summable (summable_norm_geom hq)
  simp only [← sub_eq_add_neg] at hm
  unfold qPochInf
  exact hm.hasProd

lemma tendsto_qPoch {a q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n => qPoch a q n) atTop (𝓝 (qPochInf a q)) :=
  (hasProd_qPochInf hq).tendsto_prod_nat

lemma qPochInf_ne_zero {a q : ℂ} (hq : ‖q‖ < 1) (h : ∀ k : ℕ, a * q ^ k ≠ 1) :
    qPochInf a q ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable (f := fun k : ℕ => -(a * q ^ k))
    (fun k => by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr (h k).symm)
    (summable_norm_geom hq)
  unfold qPochInf
  simpa only [← sub_eq_add_neg] using this

lemma qPochInf_shift {a q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochInf a q = qPoch a q n * qPochInf (a * q ^ n) q := by
  have h1 : Tendsto (fun N => qPoch a q (N + n)) atTop (𝓝 (qPochInf a q)) :=
    (tendsto_qPoch hq).comp (tendsto_add_atTop_nat n)
  have h2 : Tendsto (fun N => qPoch a q (N + n)) atTop
      (𝓝 (qPoch a q n * qPochInf (a * q ^ n) q)) := by
    refine ((tendsto_qPoch hq).const_mul (qPoch a q n)).congr (fun N => ?_)
    rw [add_comm, qPoch_add]
  exact tendsto_nhds_unique h1 h2

lemma bdd_of_tendsto {u : ℕ → ℂ} {L : ℂ} (h : Tendsto u atTop (𝓝 L)) :
    ∃ K, ∀ n, ‖u n‖ ≤ K := by
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto u h)
  exact ⟨K, fun n => hK _ (Set.mem_range_self n)⟩

/-- coefficient of the q-binomial series -/
noncomputable def C (A q : ℂ) (n : ℕ) : ℂ := qPoch A q n / qPoch q q n

lemma qq_ne {q : ℂ} (hq : ‖q‖ < 1) : ∀ k : ℕ, q * q ^ k ≠ 1 := ne_one_of_norm hq hq.le

lemma C_tendsto {A q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (C A q) atTop (𝓝 (qPochInf A q / qPochInf q q)) :=
  (tendsto_qPoch hq).div (tendsto_qPoch hq) (qPochInf_ne_zero hq (qq_ne hq))

lemma C_bdd (A : ℂ) {q : ℂ} (hq : ‖q‖ < 1) : ∃ K, ∀ n, ‖C A q n‖ ≤ K :=
  bdd_of_tendsto (C_tendsto hq)

lemma C_zero (A q : ℂ) : C A q 0 = 1 := by simp [C, qPoch]

lemma C_rec {A q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    C A q (n + 1) * (1 - q ^ (n + 1)) = C A q n * (1 - A * q ^ n) := by
  have h0 := qPoch_ne_zero (qq_ne hq) n
  have h1 : 1 - q * q ^ n ≠ 0 := sub_ne_zero.mpr (qq_ne hq n).symm
  have h1' : 1 - q ^ n * q ≠ 0 := by rw [mul_comm]; exact h1
  have e : (1 : ℂ) - q ^ (n + 1) = 1 - q * q ^ n := by ring
  unfold C
  rw [qPoch_succ, qPoch_succ, e]
  field_simp

noncomputable def F (A q w : ℂ) : ℂ := ∑' n, C A q n * w ^ n

lemma summable_C {A q w : ℂ} (hq : ‖q‖ < 1) (hw : ‖w‖ < 1) :
    Summable (fun n => C A q n * w ^ n) := by
  obtain ⟨K, hK⟩ := C_bdd A hq
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hw).mul_left K) ?_
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hK n) (by positivity)

lemma F_feq {A q w : ℂ} (hq : ‖q‖ < 1) (hw : ‖w‖ < 1) :
    (1 - w) * F A q w = (1 - A * w) * F A q (q * w) := by
  have hqw : ‖q * w‖ < 1 := by
    rw [norm_mul]; nlinarith [norm_nonneg q, norm_nonneg w]
  have hf := summable_C (A := A) hq hw
  have hg := summable_C (A := A) hq hqw
  have hf1 : Summable (fun n => C A q (n + 1) * w ^ (n + 1)) :=
    hf.comp_injective (add_left_injective 1)
  have hg1 : Summable (fun n => C A q (n + 1) * (q * w) ^ (n + 1)) :=
    hg.comp_injective (add_left_injective 1)
  have e1 : (1 - w) * F A q w =
      1 + ∑' n : ℕ, (C A q (n + 1) * w ^ (n + 1) - w * (C A q n * w ^ n)) := by
    rw [Summable.tsum_sub hf1 (hf.mul_left w), tsum_mul_left, F, hf.tsum_eq_zero_add]
    simp only [C_zero, pow_zero, mul_one]
    ring
  have e2 : (1 - A * w) * F A q (q * w) =
      1 + ∑' n : ℕ, (C A q (n + 1) * (q * w) ^ (n + 1) - A * w * (C A q n * (q * w) ^ n)) := by
    rw [Summable.tsum_sub hg1 (hg.mul_left (A * w)), tsum_mul_left, F, hg.tsum_eq_zero_add]
    simp only [C_zero, pow_zero, mul_one]
    ring
  rw [e1, e2]
  congr 1
  refine tsum_congr (fun n => ?_)
  linear_combination w ^ (n + 1) * C_rec (A := A) hq n

lemma F_iter {A q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (N : ℕ) :
    qPoch z q N * F A q z = qPoch (A * z) q N * F A q (z * q ^ N) := by
  induction N with
  | zero => simp [qPoch]
  | succ N ih =>
    have hw : ‖z * q ^ N‖ < 1 := lt_of_le_of_lt (norm_mul_pow_le hq.le N) hz
    have fe := F_feq (A := A) hq hw
    rw [show q * (z * q ^ N) = z * q ^ (N + 1) by ring] at fe
    rw [qPoch_succ, qPoch_succ]
    linear_combination (1 - z * q ^ N) * ih + qPoch (A * z) q N * fe

lemma F_tendsto_one {A q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => F A q (z * q ^ N)) atTop (𝓝 1) := by
  obtain ⟨K, hK⟩ := C_bdd A hq
  have key := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (n : ℕ) => C A q n * (z * q ^ N) ^ n)
    (g := fun n => C A q n * (z * 0) ^ n)
    (bound := fun n => K * ‖z‖ ^ n)
    ((summable_geometric_of_lt_one (norm_nonneg _) hz).mul_left K)
    (fun n => ((((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul z).pow n).const_mul
      (C A q n)))
    (Eventually.of_forall (fun N n => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hK n) (pow_le_pow_left₀ (norm_nonneg _) (norm_mul_pow_le hq.le N) n)
        (by positivity) ((norm_nonneg _).trans (hK n))))
  have h1 : ∑' n, C A q n * (z * 0) ^ n = 1 := by
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    simp [C_zero]
  simp only [h1] at key
  exact key

theorem qbinom {A q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n => C A q n * z ^ n) (qPochInf (A * z) q / qPochInf z q) := by
  have hI : qPochInf z q ≠ 0 := qPochInf_ne_zero hq (ne_one_of_norm hz hq.le)
  have h1 : Tendsto (fun N => qPoch z q N * F A q z) atTop (𝓝 (qPochInf z q * F A q z)) :=
    (tendsto_qPoch hq).mul_const _
  have h2 : Tendsto (fun N => qPoch z q N * F A q z) atTop (𝓝 (qPochInf (A * z) q * 1)) := by
    simp only [F_iter (A := A) hq hz]
    exact (tendsto_qPoch hq).mul (F_tendsto_one hq hz)
  have := tendsto_nhds_unique h1 h2
  have hF : F A q z = qPochInf (A * z) q / qPochInf z q := by
    rw [eq_div_iff hI, mul_comm, this, mul_one]
  rw [← hF]
  exact (summable_C hq hz).hasSum

lemma fiber_m {b c q : ℂ} (h : ℕ) (hq : ‖q‖ < 1) (hb : ‖b‖ < 1) (hb0 : b ≠ 0) (m : ℕ) :
    HasSum (fun n => C (c / b) q n * (b * q ^ (h * m)) ^ n)
      (qPochInf (c * q ^ (h * m)) q / qPochInf (b * q ^ (h * m)) q) := by
  have hz : ‖b * q ^ (h * m)‖ < 1 := lt_of_le_of_lt (norm_mul_pow_le hq.le _) hb
  have e : c / b * (b * q ^ (h * m)) = c * q ^ (h * m) := by field_simp
  have := qbinom (A := c / b) hq hz
  rwa [e] at this

lemma u_eq {a b c t q : ℂ} (h : ℕ) (hq : ‖q‖ < 1) (hb : ‖b‖ < 1)
    (hc : ∀ j : ℕ, c * q ^ j ≠ 1) (m : ℕ) :
    qPoch a (q ^ h) m * qPoch b q (h * m) * t ^ m /
      (qPoch (q ^ h) (q ^ h) m * qPoch c q (h * m)) =
    qPochInf b q / qPochInf c q * (C a (q ^ h) m * t ^ m *
      (qPochInf (c * q ^ (h * m)) q / qPochInf (b * q ^ (h * m)) q)) := by
  have hIc : qPochInf c q ≠ 0 := qPochInf_ne_zero hq hc
  have hsb := qPochInf_shift (a := b) hq (h * m)
  have hsc := qPochInf_shift (a := c) hq (h * m)
  have hbX : qPochInf (b * q ^ (h * m)) q ≠ 0 :=
    qPochInf_ne_zero hq (ne_one_of_norm (lt_of_le_of_lt (norm_mul_pow_le hq.le _) hb) hq.le)
  have hcX : qPochInf (c * q ^ (h * m)) q ≠ 0 := fun h0 => hIc (by rw [hsc, h0, mul_zero])
  have hPc : qPoch c q (h * m) ≠ 0 := qPoch_ne_zero hc _
  by_cases hPQ : qPoch (q ^ h) (q ^ h) m = 0
  · simp [C, hPQ]
  rw [hsb, hsc]
  unfold C
  generalize qPochInf (c * q ^ (h * m)) q = X at *
  generalize qPochInf (b * q ^ (h * m)) q = Y at *
  field_simp

lemma fiber_n {a b c t q : ℂ} (h : ℕ) (hq : ‖q‖ < 1) (hQ : ‖q ^ h‖ < 1) (ht : ‖t‖ < 1)
    (hat : ∀ j : ℕ, a * t * (q ^ h) ^ j ≠ 1) (n : ℕ) :
    HasSum (fun m => C a (q ^ h) m * t ^ m * (C (c / b) q n * (b * q ^ (h * m)) ^ n))
      (qPochInf (a * t) (q ^ h) / qPochInf t (q ^ h) *
        (qPoch (c / b) q n * qPoch t (q ^ h) n * b ^ n /
          (qPoch q q n * qPoch (a * t) (q ^ h) n))) := by
  have hz : ‖t * (q ^ h) ^ n‖ < 1 := lt_of_le_of_lt (norm_mul_pow_le hQ.le _) ht
  have hs := (qbinom (A := a) hQ hz).mul_left (C (c / b) q n * b ^ n)
  have e1 : a * (t * (q ^ h) ^ n) = a * t * (q ^ h) ^ n := by ring
  rw [e1] at hs
  have hsa := qPochInf_shift (a := a * t) hQ n
  have hst := qPochInf_shift (a := t) hQ n
  have hIt : qPochInf (t * (q ^ h) ^ n) (q ^ h) ≠ 0 := qPochInf_ne_zero hQ (ne_one_of_norm hz hQ.le)
  have hPt : qPoch t (q ^ h) n ≠ 0 := qPoch_ne_zero (ne_one_of_norm ht hQ.le) n
  have hPat : qPoch (a * t) (q ^ h) n ≠ 0 := qPoch_ne_zero hat n
  have hPq : qPoch q q n ≠ 0 := qPoch_ne_zero (qq_ne hq) n
  have hf : (fun m => C a (q ^ h) m * t ^ m * (C (c / b) q n * (b * q ^ (h * m)) ^ n)) =
      (fun i => C (c / b) q n * b ^ n * (C a (q ^ h) i * (t * (q ^ h) ^ n) ^ i)) := by
    funext m
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, show h * m * n = h * n * m by ring]
    ring
  have hval : qPochInf (a * t) (q ^ h) / qPochInf t (q ^ h) *
        (qPoch (c / b) q n * qPoch t (q ^ h) n * b ^ n /
          (qPoch q q n * qPoch (a * t) (q ^ h) n)) =
      C (c / b) q n * b ^ n * (qPochInf (a * t * (q ^ h) ^ n) (q ^ h) /
        qPochInf (t * (q ^ h) ^ n) (q ^ h)) := by
    rw [hsa, hst]
    unfold C
    generalize qPochInf (a * t * (q ^ h) ^ n) (q ^ h) = X at *
    generalize qPochInf (t * (q ^ h) ^ n) (q ^ h) = Y at *
    field_simp
  rw [hf, hval]
  exact hs

lemma main (a b c t q : ℂ) (h : ℕ) (hh : 0 < h)
    (hq : ‖q‖ < 1) (ht : ‖t‖ < 1) (hb : ‖b‖ < 1) (hb0 : b ≠ 0)
    (hc : ∀ j : ℕ, c * q ^ j ≠ 1)
    (hat : ∀ j : ℕ, a * t * (q ^ h) ^ j ≠ 1) :
    Summable (fun m : ℕ => qPoch a (q ^ h) m * qPoch b q (h * m) * t ^ m /
      (qPoch (q ^ h) (q ^ h) m * qPoch c q (h * m))) ∧
    Summable (fun m : ℕ => qPoch (c / b) q m * qPoch t (q ^ h) m * b ^ m /
      (qPoch q q m * qPoch (a * t) (q ^ h) m)) ∧
    (∑' m : ℕ, qPoch a (q ^ h) m * qPoch b q (h * m) * t ^ m /
      (qPoch (q ^ h) (q ^ h) m * qPoch c q (h * m))) =
      qPochInf b q * qPochInf (a * t) (q ^ h) /
        (qPochInf c q * qPochInf t (q ^ h)) *
        (∑' m : ℕ, qPoch (c / b) q m * qPoch t (q ^ h) m * b ^ m /
          (qPoch q q m * qPoch (a * t) (q ^ h) m)) := by
  have hQ : ‖q ^ h‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq hh.ne'
  have hIc : qPochInf c q ≠ 0 := qPochInf_ne_zero hq hc
  have hIt : qPochInf t (q ^ h) ≠ 0 := qPochInf_ne_zero hQ (ne_one_of_norm ht hQ.le)
  have hIat : qPochInf (a * t) (q ^ h) ≠ 0 := qPochInf_ne_zero hQ hat
  obtain ⟨K1, hK1⟩ := C_bdd a hQ
  obtain ⟨K2, hK2⟩ := C_bdd (c / b) hq
  have hK1n : 0 ≤ K1 := (norm_nonneg _).trans (hK1 0)
  have hK2n : 0 ≤ K2 := (norm_nonneg _).trans (hK2 0)
  set T : ℕ × ℕ → ℂ := fun p =>
    C a (q ^ h) p.1 * t ^ p.1 * (C (c / b) q p.2 * (b * q ^ (h * p.1)) ^ p.2) with hTdef
  have hTs : Summable T := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => (K1 * ‖t‖ ^ p.1) * (K2 * ‖b‖ ^ p.2))
      (Summable.mul_of_nonneg
        ((summable_geometric_of_lt_one (norm_nonneg _) ht).mul_left K1)
        ((summable_geometric_of_lt_one (norm_nonneg _) hb).mul_left K2)
        (fun n => by positivity) (fun n => by positivity)) ?_
    rintro ⟨m, n⟩
    simp only [hTdef, norm_mul, norm_pow]
    refine mul_le_mul (mul_le_mul_of_nonneg_right (hK1 m) (by positivity))
      (mul_le_mul (hK2 n) (pow_le_pow_left₀ (by positivity) ?_ n) (by positivity) hK2n)
      (by positivity) (by positivity)
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  have hS := hTs.hasSum
  -- fibre over m
  have hu := (hS.prod_fiberwise (fun m => (fiber_m (c := c) h hq hb hb0 m).mul_left
    (C a (q ^ h) m * t ^ m))).mul_left (qPochInf b q / qPochInf c q)
  simp only [← u_eq (a := a) (t := t) h hq hb hc] at hu
  -- fibre over n
  have hS' : HasSum (T ∘ Equiv.prodComm ℕ ℕ) (∑' p, T p) := (Equiv.hasSum_iff _).mpr hS
  have hv := (hS'.prod_fiberwise (fun n => fiber_n (b := b) (c := c) h hq hQ ht hat n)).mul_left
    (qPochInf (a * t) (q ^ h) / qPochInf t (q ^ h))⁻¹
  have hL : qPochInf (a * t) (q ^ h) / qPochInf t (q ^ h) ≠ 0 := div_ne_zero hIat hIt
  simp only [← mul_assoc, inv_mul_cancel₀ hL, one_mul] at hv
  refine ⟨hu.summable, hv.summable, ?_⟩
  rw [hu.tsum_eq, hv.tsum_eq]
  field_simp

end S100R121

open RamanujanLostNotebook.PartII in
theorem solution (a b c t q : ℂ) (h : ℕ) (hh : 0 < h)
    (hq : ‖q‖ < 1) (ht : ‖t‖ < 1) (hb : ‖b‖ < 1) (hb0 : b ≠ 0)
    (hc : ∀ j : ℕ, c * q ^ j ≠ 1)
    (hat : ∀ j : ℕ, a * t * (q ^ h) ^ j ≠ 1) :
    Summable (fun m : ℕ => qPoch a (q ^ h) m * qPoch b q (h * m) * t ^ m /
      (qPoch (q ^ h) (q ^ h) m * qPoch c q (h * m))) ∧
    Summable (fun m : ℕ => qPoch (c / b) q m * qPoch t (q ^ h) m * b ^ m /
      (qPoch q q m * qPoch (a * t) (q ^ h) m)) ∧
    (∑' m : ℕ, qPoch a (q ^ h) m * qPoch b q (h * m) * t ^ m /
      (qPoch (q ^ h) (q ^ h) m * qPoch c q (h * m))) =
      qPochInf b q * qPochInf (a * t) (q ^ h) /
        (qPochInf c q * qPochInf t (q ^ h)) *
        (∑' m : ℕ, qPoch (c / b) q m * qPoch t (q ^ h) m * b ^ m /
          (qPoch q q m * qPoch (a * t) (q ^ h) m)) :=
  S100R121.main a b c t q h hh hq ht hb hb0 hc hat

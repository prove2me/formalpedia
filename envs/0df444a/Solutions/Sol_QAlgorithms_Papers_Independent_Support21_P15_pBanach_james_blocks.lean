-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P15.pBanach_james_blocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:20:19.888219+00:00
-- url     : https://prove2.me/submissions/7152b979-e5f1-4eec-a2d9-84e5b8f9772f

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P15
noncomputable section
open scoped BigOperators
open Filter
open QAlgorithms.Papers.Independent.Support21.P15

def g66i_Np (p : ℝ) (c : ℕ →₀ ℂ) : ℝ := c.sum (fun _ z => ‖z‖ ^ p)

lemma g66i_Np_nonneg (p : ℝ) (c : ℕ →₀ ℂ) : 0 ≤ g66i_Np p c :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)

lemma g66i_Np_pos (p : ℝ) (c : ℕ →₀ ℂ) (hc : c ≠ 0) : 0 < g66i_Np p c := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hc
  have h1 : 0 < ‖c i‖ ^ p := Real.rpow_pos_of_pos (norm_pos_iff.mpr (Finsupp.mem_support_iff.mp hi)) _
  have h2 : ‖c i‖ ^ p ≤ g66i_Np p c :=
    Finset.single_le_sum (f := fun j => ‖c j‖ ^ p) (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) hi
  linarith

lemma g66i_Np_smul (p : ℝ) (hp : 0 < p) (t : ℂ) (c : ℕ →₀ ℂ) :
    g66i_Np p (t • c) = ‖t‖ ^ p * g66i_Np p c := by
  unfold g66i_Np
  rw [Finsupp.sum_smul_index' (fun _ => by simp [Real.zero_rpow hp.ne'])]
  rw [Finsupp.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

lemma g66i_V_eq {E : Type*} [AddCommGroup E] [Module ℂ E] (b : ℕ → E) (c : ℕ →₀ ℂ) :
    coefficientVector b c = Finsupp.linearCombination ℂ b c :=
  (Finsupp.linearCombination_apply ℂ c).symm

lemma g66i_size_zero {E : Type*} [AddCommGroup E] [Module ℂ E] (g : ComplexQuasiNorm E) :
    g.size 0 = 0 := (g.eq_zero 0).mpr rfl

lemma g66i_psum {E : Type*} [AddCommGroup E] [Module ℂ E] (p : ℝ) (hp : 0 < p)
    (g : ComplexQuasiNorm E)
    (hs : ∀ x y, g.size (x + y) ^ p ≤ g.size x ^ p + g.size y ^ p)
    {ι : Type*} (s : Finset ι) (y : ι → E) :
    g.size (∑ k ∈ s, y k) ^ p ≤ ∑ k ∈ s, g.size (y k) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [g66i_size_zero, Real.zero_rpow hp.ne']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hs _ _).trans (by linarith)

theorem solution
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (g : ComplexQuasiNorm E) (hE : IsSourcePBanach p g)
    (b : ℕ → E) (hBasis : GaugeSpanning g b)
    (hEquivalent : ∃ K : ℝ, 1 ≤ K ∧ EquivalentLp p K g b) :
    ∀ eps : ℝ, 0 < eps → ∃ c : ℕ → (ℕ →₀ ℂ),
      SuccessiveBlocks c ∧
      EquivalentLp p (1 + eps) g (fun n => coefficientVector b (c n)) := by
  intro eps heps
  obtain ⟨K, hK1, lo0, hlo0, hi0, hhi0, hK, hb⟩ := hEquivalent
  have hs : ∀ x y, g.size (x + y) ^ p ≤ g.size x ^ p + g.size y ^ p := by
    have h2 := hE.2
    split_ifs at h2 with h1
    · have : p = 1 := le_antisymm hp1 h1
      subst this; simpa using h2
    · exact h2
  let N : (ℕ →₀ ℂ) → ℝ := fun c => g66i_Np p c ^ (1/p)
  have hN : ∀ c, coefficientLpSize p c = N c := fun c => rfl
  let Sset : ℕ → Set ℝ := fun M => {r | ∃ C : ℕ →₀ ℂ, C ≠ 0 ∧ (∀ i ∈ C.support, M ≤ i) ∧
    r = g.size (coefficientVector b C) / N C}
  have hNpos : ∀ C : ℕ →₀ ℂ, C ≠ 0 → 0 < N C :=
    fun C hC => Real.rpow_pos_of_pos (g66i_Np_pos p C hC) _
  have hne : ∀ M, (Sset M).Nonempty := by
    intro M
    refine ⟨_, Finsupp.single M 1, by simp, ?_, rfl⟩
    intro i hi
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hi
    omega
  have hlow : ∀ M, ∀ r ∈ Sset M, lo0 ≤ r := by
    rintro M r ⟨C, hC, -, rfl⟩
    rw [le_div_iff₀ (hNpos C hC)]; exact (hb C).1
  have hup : ∀ M, ∀ r ∈ Sset M, r ≤ hi0 := by
    rintro M r ⟨C, hC, -, rfl⟩
    rw [div_le_iff₀ (hNpos C hC)]; exact (hb C).2
  have hbdd : ∀ M, BddBelow (Sset M) := fun M => ⟨lo0, hlow M⟩
  let lam : ℕ → ℝ := fun M => sInf (Sset M)
  have hlam_lo : ∀ M, lo0 ≤ lam M := fun M => le_csInf (hne M) (hlow M)
  have hlam_hi : ∀ M, lam M ≤ hi0 :=
    fun M => (csInf_le (hbdd M) (hne M).some_mem).trans (hup M _ (hne M).some_mem)
  have hbddA : BddAbove (Set.range lam) := ⟨hi0, by rintro _ ⟨M, rfl⟩; exact hlam_hi M⟩
  set Λ := ⨆ M, lam M with hΛdef
  have hΛ : ∀ M, lam M ≤ Λ := fun M => le_ciSup hbddA M
  have hΛpos : 0 < Λ := lt_of_lt_of_le hlo0 ((hlam_lo 0).trans (hΛ 0))
  set δ := min eps 1 / 3 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 3 := by
    have := min_le_right eps 1; rw [hδdef]; linarith
  have hδe : 3 * δ ≤ eps := by
    have := min_le_left eps 1; rw [hδdef]; linarith
  have hlt : Λ / (1 + δ) < Λ := div_lt_self hΛpos (by linarith)
  obtain ⟨N0, hN0⟩ := exists_lt_of_lt_ciSup hlt
  have hblk : ∀ M, ∃ c : ℕ →₀ ℂ, (∀ i ∈ c.support, max M N0 ≤ i) ∧ c.support.Nonempty ∧
      g66i_Np p c = 1 ∧ g.size (coefficientVector b c) ≤ Λ * (1 + δ) := by
    intro M
    have hpos := hlo0.trans_le (hlam_lo (max M N0))
    have hl : lam (max M N0) < lam (max M N0) * (1 + δ) := by nlinarith
    obtain ⟨r, ⟨C, hC, hsupp, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (hne (max M N0)) hl
    have hNC := hNpos C hC
    set t : ℝ := (N C)⁻¹ with ht
    have htpos : 0 < t := inv_pos.mpr hNC
    refine ⟨(t : ℂ) • C, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact hsupp i (Finsupp.support_smul hi)
    · rw [Finsupp.support_smul_eq (by exact_mod_cast htpos.ne')]
      exact Finsupp.support_nonempty_iff.mpr hC
    · rw [g66i_Np_smul p hp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht,
        Real.inv_rpow hNC.le, ← Real.rpow_mul (g66i_Np_nonneg p C), one_div_mul_cancel hp.ne',
        Real.rpow_one]
      exact inv_mul_cancel₀ (g66i_Np_pos p C hC).ne'
    · rw [g66i_V_eq, map_smul, g.smul_size, ← g66i_V_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos htpos, ht, inv_mul_eq_div]
      exact hr.le.trans (mul_le_mul_of_nonneg_right (hΛ _) (by linarith))
  choose blk hblk using hblk
  let Mseq : ℕ → ℕ := fun k => Nat.rec N0 (fun _ m => (blk m).support.max' (hblk m).2.1 + 1) k
  have hMs : ∀ k, Mseq (k+1) = (blk (Mseq k)).support.max' (hblk _).2.1 + 1 := fun k => rfl
  let c := fun k => blk (Mseq k)
  have hcsupp : ∀ k, ∀ i ∈ (c k).support, max (Mseq k) N0 ≤ i ∧ i < Mseq (k+1) := by
    intro k i hi
    refine ⟨(hblk _).1 i hi, ?_⟩
    rw [hMs]
    exact Nat.lt_succ_of_le (Finset.le_max' _ i hi)
  have hstep : ∀ k, Mseq k < Mseq (k+1) := by
    intro k
    obtain ⟨i, hi⟩ := (hblk (Mseq k)).2.1
    have := hcsupp k i hi
    omega
  have hMmono : StrictMono Mseq := strictMono_nat_of_lt_succ hstep
  have hdisj : ∀ m n, m ≠ n → ∀ i ∈ (c m).support, i ∉ (c n).support := by
    intro m n hmn i hi hi'
    have h1 := hcsupp m i hi
    have h2 := hcsupp n i hi'
    rcases Nat.lt_or_gt_of_ne hmn with h | h
    · have := hMmono.monotone (show m + 1 ≤ n by omega)
      omega
    · have := hMmono.monotone (show n + 1 ≤ m by omega)
      omega
  refine ⟨c, ⟨fun n => (hblk _).2.1, ?_⟩, ?_⟩
  · intro n i hi j hj
    have h1 := hcsupp n i hi
    have h2 := hcsupp (n+1) j hj
    omega
  refine ⟨lam N0, hlo0.trans_le (hlam_lo N0), Λ * (1 + δ), by positivity, ?_, ?_⟩
  · have h1 : Λ < lam N0 * (1 + δ) := (div_lt_iff₀ (by linarith)).mp hN0
    have h2 : (1 + δ) ^ 2 ≤ 1 + eps := by nlinarith
    have h3 := hlo0.trans_le (hlam_lo N0)
    nlinarith
  intro a
  set C : ℕ →₀ ℂ := ∑ n ∈ a.support, a n • c n with hCdef
  have hVa : coefficientVector (fun n => coefficientVector b (c n)) a = coefficientVector b C := by
    rw [g66i_V_eq b C, hCdef, map_sum]
    show (∑ n ∈ a.support, a n • coefficientVector b (c n)) = _
    apply Finset.sum_congr rfl
    intro n _
    rw [map_smul, g66i_V_eq]
  have hCval : ∀ n ∈ a.support, ∀ i ∈ (c n).support, C i = a n * c n i := by
    intro n hn i hi
    rw [hCdef, Finsupp.finset_sum_apply, Finset.sum_eq_single n]
    · simp
    · intro m _ hmn
      simp [Finsupp.notMem_support_iff.mp (hdisj n m (Ne.symm hmn) i hi)]
    · intro h; exact absurd hn h
  have hCsupp : C.support ⊆ a.support.biUnion (fun n => (c n).support) := by
    rw [hCdef]
    refine Finsupp.support_finset_sum.trans ?_
    exact Finset.biUnion_mono (fun n _ => Finsupp.support_smul)
  have hNpC : g66i_Np p C = g66i_Np p a := by
    unfold g66i_Np
    rw [Finsupp.sum_of_support_subset C hCsupp _ (fun _ _ => by simp [Real.zero_rpow hp.ne'])]
    rw [Finset.sum_biUnion]
    · unfold Finsupp.sum
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [hCval n hn i hi, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)])]
      rw [← Finset.mul_sum]
      have := (hblk (Mseq n)).2.2.1
      unfold g66i_Np Finsupp.sum at this
      rw [this, mul_one]
    · intro m _ n _ hmn
      exact Finset.disjoint_left.mpr (fun i hi hi' => hdisj m n hmn i hi hi')
  constructor
  · rw [hVa, hN]
    by_cases ha : a = 0
    · have : N a = 0 := by
        simp only [N, ha, g66i_Np, Finsupp.sum_zero_index]
        exact Real.zero_rpow (by positivity)
      rw [this, mul_zero]; exact g.nonneg _
    · have hC0 : C ≠ 0 := by
        intro h
        have := g66i_Np_pos p a ha
        rw [← hNpC, h] at this
        simp [g66i_Np] at this
      have hmem : g.size (coefficientVector b C) / N C ∈ Sset N0 := by
        refine ⟨C, hC0, fun i hi => ?_, rfl⟩
        obtain ⟨n, -, hn⟩ := Finset.mem_biUnion.mp (hCsupp hi)
        exact (le_max_right _ _).trans (hcsupp n i hn).1
      have := csInf_le (hbdd N0) hmem
      rw [le_div_iff₀ (hNpos C hC0)] at this
      have hNa : N a = N C := by simp only [N, hNpC]
      rw [hNa]; exact this
  · rw [hN]
    have key : g.size (coefficientVector (fun n => coefficientVector b (c n)) a) ^ p ≤
        (Λ * (1 + δ)) ^ p * g66i_Np p a := by
      rw [show coefficientVector (fun n => coefficientVector b (c n)) a =
        ∑ n ∈ a.support, a n • coefficientVector b (c n) from rfl]
      refine (g66i_psum p hp g hs _ _).trans ?_
      unfold g66i_Np Finsupp.sum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      rw [g.smul_size, Real.mul_rpow (norm_nonneg _) (g.nonneg _), mul_comm]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      exact Real.rpow_le_rpow (g.nonneg _) (hblk _).2.2.2 hp.le
    have hH : 0 ≤ Λ * (1 + δ) := by positivity
    have := Real.rpow_le_rpow (Real.rpow_nonneg (g.nonneg _) _) key (one_div_nonneg.mpr hp.le)
    rw [← Real.rpow_mul (g.nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one,
      Real.mul_rpow (Real.rpow_nonneg hH _) (g66i_Np_nonneg p a), ← Real.rpow_mul hH,
      mul_one_div_cancel hp.ne', Real.rpow_one] at this
    exact this

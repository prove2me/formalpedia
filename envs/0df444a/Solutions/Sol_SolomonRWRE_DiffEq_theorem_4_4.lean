-- Prove2me | solution 1 for SolomonRWRE.DiffEq.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T01:41:26.102984+00:00
-- url     : https://prove2.me/submissions/d4aab499-fa40-423e-838e-c48a17b773e8

-- Complete checked reconstruction of the native Solomon random-recurrence strong law.
-- Licensed under Apache 2.0.
import Definitions.Def_SolomonRWRE_DiffEq_System
import Mathlib


-- Begin SequenceBasic

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

/-- A block starts at zero-indexed position `j` and has length `k`. -/
def block (x : ℕ → ℝ) (j k : ℕ) : ℝ := ∏ i ∈ range k, x (j+i)

lemma block_zero (x : ℕ → ℝ) (j : ℕ) : block x j 0 = 1 := by simp [block]
lemma block_succ (x : ℕ → ℝ) (j k : ℕ) :
    block x j (k+1) = block x j k * x (j+k) := by simp [block, prod_range_succ]
lemma block_one (x : ℕ → ℝ) (j : ℕ) : block x j 1 = x j := by simp [block]
lemma block_nonneg {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (j k : ℕ) :
    0 ≤ block x j k := Finset.prod_nonneg fun _ _ => hx _
lemma block_mono {x y : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i)
    (j k : ℕ) : block x j k ≤ block y j k := by
  exact Finset.prod_le_prod (fun _ _ => hx _) (fun _ _ => hxy _)
lemma block_le_pow {x : ℕ → ℝ} {R : ℝ} (hx : ∀ i, 0 ≤ x i)
    (hR : ∀ i, x i ≤ R) (j k : ℕ) : block x j k ≤ R^k := by
  simpa [block] using block_mono hx hR j k

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma block_measurable {x : ℕ → Ω → ℝ} (hx : ∀ i, Measurable (x i)) (j k : ℕ) :
    Measurable (fun ω => block (fun i => x i ω) j k) := by
  exact Finset.measurable_prod _ fun _ _ => hx _

omit [MeasurableSpace Ω] in
lemma Z_nonneg {σ : ℕ → Ω → ℝ} (hσ : ∀ n ω, 0 ≤ σ (n+1) ω) (n : ℕ) (ω : Ω) :
    0 ≤ Z σ n ω := by
  induction n with
  | zero => simp [Z]
  | succ n ih => exact mul_nonneg (hσ n ω) (by linarith)

omit [MeasurableSpace Ω] in
lemma Z_mono {σ τ : ℕ → Ω → ℝ} (hσ : ∀ n ω, 0 ≤ σ (n+1) ω)
    (hστ : ∀ n ω, σ (n+1) ω ≤ τ (n+1) ω) (n : ℕ) (ω : Ω) :
    Z σ n ω ≤ Z τ n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact mul_le_mul (hστ n ω) (by linarith) (by linarith [Z_nonneg hσ n ω])
      (le_trans (hσ n ω) (hστ n ω))

lemma Z_measurable {σ : ℕ → Ω → ℝ} (hσ : ∀ n, Measurable (σ (n+1))) (n : ℕ) :
    Measurable (Z σ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hσ n).mul (measurable_const.add ih)

end SolomonRWRE.DiffEq.Proof
-- End SequenceBasic

-- Begin BlockLaw

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {x : ℕ → Ω → ℝ}

lemma block_eq_finprod (x : ℕ → ℝ) (j k : ℕ) :
    block x j k = ∏ i : Fin k, x (j+i) := by
  exact (Fin.prod_univ_eq_prod_range (fun i => x (j+i)) k).symm

lemma block_eq_Ico (x : ℕ → ℝ) (j k : ℕ) :
    block x j k = ∏ i ∈ Ico j (j+k), x i := by
  rw [prod_Ico_eq_prod_range]
  simp [block]

lemma block_ident (hx : iIndepFun x P) (hi : ∀ i, IdentDistrib (x i) (x 0) P P)
    (j l k : ℕ) :
    IdentDistrib (fun ω => block (fun i => x i ω) j k)
      (fun ω => block (fun i => x i ω) l k) P P := by
  have hj : Function.Injective (fun i : Fin k => j+(i:ℕ)) := by
    intro a b h
    apply Fin.ext
    dsimp only at h
    omega
  have hl : Function.Injective (fun i : Fin k => l+(i:ℕ)) := by
    intro a b h
    apply Fin.ext
    dsimp only at h
    omega
  have h := IdentDistrib.pi (fun i : Fin k => (hi (j+i)).trans (hi (l+i)).symm)
    (hx.precomp hj) (hx.precomp hl)
  have hh := h.comp (show Measurable (fun z : Fin k → ℝ => ∏ i, z i) by fun_prop)
  simp_rw [block_eq_finprod]
  exact hh

lemma block_integral (hx : iIndepFun x P) (hm : ∀ i, Measurable (x i))
    (hi : ∀ i, IdentDistrib (x i) (x 0) P P) (j k : ℕ) :
    (∫ ω, block (fun i => x i ω) j k ∂P) = (∫ ω, x 0 ω ∂P)^k := by
  have hj : Function.Injective (fun i : Fin k => j+(i:ℕ)) := by
    intro a b h
    apply Fin.ext
    dsimp only at h
    omega
  simp_rw [block_eq_finprod]
  rw [(hx.precomp hj).integral_fun_prod_eq_prod_integral (fun i => (hm _).aestronglyMeasurable)]
  simp_rw [(hi _).integral_eq]
  simp

lemma block_indep (hx : iIndepFun x P) (hm : ∀ i, Measurable (x i))
    (j l k : ℕ) (hd : Disjoint (Ico j (j+k)) (Ico l (l+k))) :
    IndepFun (fun ω => block (fun i => x i ω) j k)
      (fun ω => block (fun i => x i ω) l k) P := by
  classical
  have h := hx.indepFun_finset (Ico j (j+k)) (Ico l (l+k)) hd hm
  have hh := h.comp
    (show Measurable (fun z : (Ico j (j+k) : Finset ℕ) → ℝ => ∏ i, z i) by fun_prop)
    (show Measurable (fun z : (Ico l (l+k) : Finset ℕ) → ℝ => ∏ i, z i) by fun_prop)
  simp_rw [block_eq_Ico]
  have hj : (fun ω => ∏ i : (Ico j (j+k) : Finset ℕ), x i ω) =
      (fun ω => ∏ i ∈ Ico j (j+k), x i ω) := by
    funext ω
    exact Finset.prod_coe_sort (Ico j (j+k)) (fun i : ℕ => x i ω)
  have hl : (fun ω => ∏ i : (Ico l (l+k) : Finset ℕ), x i ω) =
      (fun ω => ∏ i ∈ Ico l (l+k), x i ω) := by
    funext ω
    exact Finset.prod_coe_sort (Ico l (l+k)) (fun i : ℕ => x i ω)
  change IndepFun (fun ω => ∏ i : (Ico j (j+k) : Finset ℕ), x i ω)
    (fun ω => ∏ i : (Ico l (l+k) : Finset ℕ), x i ω) P at hh
  rw [hj, hl] at hh
  exact hh

end SolomonRWRE.DiffEq.Proof
-- End BlockLaw

-- Begin BlockStrongLaw

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

lemma disjoint_residue_intervals (k r q s : ℕ) (hqs : q ≠ s) :
    Disjoint (Ico (k*q+r) (k*q+r+k)) (Ico (k*s+r) (k*s+r+k)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [mem_Ico] at hi hj
  rcases lt_or_gt_of_ne hqs with h | h
  · have hh := Nat.mul_le_mul_left k (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at hh
    omega
  · have hh := Nat.mul_le_mul_left k (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at hh
    omega

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {x : ℕ → Ω → ℝ}

lemma bounded_block_integrable (hm : ∀ i, Measurable (x i))
    (hn : ∀ i ω, 0 ≤ x i ω) {B : ℝ} (hb : ∀ i ω, x i ω ≤ B) (j k : ℕ) :
    Integrable (fun ω => block (fun i => x i ω) j k) P := by
  apply Integrable.mono' (integrable_const (B^k)) (block_measurable hm j k).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (block_nonneg (fun i => hn i ω) j k)]
    exact block_le_pow (fun i => hn i ω) (fun i => hb i ω) j k

lemma residue_block_strongLaw (hm : ∀ i, Measurable (x i))
    (hn : ∀ i ω, 0 ≤ x i ω) (hx : iIndepFun x P)
    (hi : ∀ i, IdentDistrib (x i) (x 0) P P) {B : ℝ}
    (hb : ∀ i ω, x i ω ≤ B) (k r : ℕ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (∑ q ∈ range n, block (fun i => x i ω) (k*q+r) k) / n) atTop
        (𝓝 ((∫ ω, x 0 ω ∂P)^k)) := by
  let X := fun q ω => block (fun i => x i ω) (k*q+r) k
  have hind : Pairwise (fun q s => IndepFun (X q) (X s) P) := by
    intro q s hqs
    exact block_indep hx hm _ _ _ (disjoint_residue_intervals k r q s hqs)
  have hident : ∀ q, IdentDistrib (X q) (X 0) P P := fun q => block_ident hx hi _ _ _
  have h := strong_law_ae_real X (bounded_block_integrable hm hn hb _ _) hind hident
  have hmean : (∫ ω, X 0 ω ∂P) = (∫ ω, x 0 ω ∂P)^k := block_integral hx hm hi _ _
  rw [hmean] at h
  exact h

end SolomonRWRE.DiffEq.Proof
-- End BlockStrongLaw

-- Begin ResidueAverages

open Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

lemma sum_range_residues (w : ℕ → ℝ) (k q : ℕ) :
    (∑ i ∈ range (k*q), w i) = ∑ r ∈ range k, ∑ j ∈ range q, w (k*j+r) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp_rw [sum_range_succ]
    rw [sum_add_distrib]

lemma average_multiples (w : ℕ → ℝ) (k q : ℕ) :
    (∑ i ∈ range (k*q), w i) / (k*q : ℕ) =
      (∑ r ∈ range k, (∑ j ∈ range q, w (k*j+r)) / q) / k := by
  rw [sum_range_residues, ← sum_div]
  simp only [Nat.cast_mul, div_div, mul_comm]

lemma quotient_density (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => (k*(n/k) : ℕ) / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mod_div_atTop_nhds_zero_nat hk)
  have ht' : Tendsto (fun n : ℕ => 1 - (n%k : ℕ) / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : ((k*(n/k) : ℕ) : ℝ) + (n%k : ℕ) = n := by
    exact_mod_cast Nat.div_add_mod n k
  field_simp
  linarith

lemma residue_average_limit {w : ℕ → ℝ} {k : ℕ} (hk : 0 < k) {B L : ℝ}
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ B)
    (h : ∀ r < k, Tendsto (fun q : ℕ => (∑ j ∈ range q, w (k*j+r)) / q)
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (∑ j ∈ range n, w j) / n) atTop (𝓝 L) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hb : 0 ≤ B := (hw 0).1.trans (hw 0).2
  have hm : Tendsto (fun q : ℕ => (∑ i ∈ range (k*q), w i) / (k*q : ℕ))
      atTop (𝓝 L) := by
    have ht := (tendsto_finsetSum (range k) (fun r hr => h r (mem_range.mp hr))).div_const (k : ℝ)
    simp only [sum_const, card_range, nsmul_eq_mul, mul_div_cancel_left₀ L hk'] at ht
    simpa only [average_multiples] using ht
  have hq : Tendsto (fun n : ℕ => n/k) atTop atTop := Nat.tendsto_div_const_atTop (Nat.ne_of_gt hk)
  have hp : Tendsto (fun n : ℕ => (∑ i ∈ range (k*(n/k)), w i) / n) atTop (𝓝 L) := by
    have ht := (hm.comp hq).mul (quotient_density k hk)
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    have hkn : 0 < k*(n/k) := Nat.mul_pos hk (Nat.div_pos hn hk)
    have he : ((k*(n/k) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hkn
    dsimp
    field_simp
  have ht : Tendsto (fun n : ℕ => (∑ i ∈ range (n%k), w (k*(n/k)+i)) / n)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun n => div_nonneg (sum_nonneg (fun i _ => (hw _).1)) (Nat.cast_nonneg n))
      (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ)*B))
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc
      _ ≤ ∑ _i ∈ range (n%k), B := sum_le_sum (fun i _ => (hw _).2)
      _ = (n%k : ℕ)*B := by simp
      _ ≤ (k : ℝ)*B := mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt n hk).le) hb
  have hs := hp.add ht
  simp only [add_zero] at hs
  apply hs.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [← add_div, ← sum_range_add, Nat.div_add_mod]

end SolomonRWRE.DiffEq.Proof
-- End ResidueAverages

-- Begin Truncation

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {σ : ℕ → Ω → ℝ}

def trunc (σ : ℕ → Ω → ℝ) (R : ℕ) (n : ℕ) (ω : Ω) : ℝ := min (σ n ω) R

lemma iid_trunc (hσ : IsIIDNonneg P σ) (R : ℕ) : IsIIDNonneg P (trunc σ R) where
  meas n := (hσ.meas n).min measurable_const
  nonneg n ω := le_min (hσ.nonneg n ω) (Nat.cast_nonneg R)
  indep := hσ.indep.comp (fun _ z => min z (R:ℝ)) (fun _ => measurable_id.min measurable_const)
  ident n := (hσ.ident n).comp (measurable_id.min measurable_const)

omit [MeasurableSpace Ω] in
lemma trunc_le (R n : ℕ) (ω : Ω) : trunc σ R n ω ≤ σ n ω := min_le_left _ _
omit [MeasurableSpace Ω] in
lemma trunc_bound (R n : ℕ) (ω : Ω) : trunc σ R n ω ≤ R := min_le_right _ _

lemma trunc_integrable [IsProbabilityMeasure P] (hσ : IsIIDNonneg P σ) (R n : ℕ) :
    Integrable (trunc σ R (n+1)) P := by
  apply Integrable.mono' (integrable_const (R:ℝ)) ((iid_trunc hσ R).meas n).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg ((iid_trunc hσ R).nonneg n ω)]
    exact trunc_bound R (n+1) ω

lemma nu_trunc_mono : Monotone (fun R : ℕ => nu P (trunc σ R)) := by
  intro R S hRS
  exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hRS))

lemma nu_trunc_iSup (hσ : IsIIDNonneg P σ) :
    (⨆ R : ℕ, nu P (trunc σ R)) = nu P σ := by
  unfold nu
  have hm : ∀ R : ℕ, Measurable (fun ω => ENNReal.ofReal (trunc σ R 1 ω)) :=
    fun R => ENNReal.measurable_ofReal.comp ((iid_trunc hσ R).meas 0)
  rw [← lintegral_iSup hm]
  · apply lintegral_congr
    intro ω
    apply le_antisymm
    · exact iSup_le fun R => ENNReal.ofReal_le_ofReal (trunc_le R 1 ω)
    · obtain ⟨R,hR⟩ := exists_nat_ge (σ 1 ω)
      exact le_iSup_of_le R (by simp [trunc, min_eq_left hR])
  · intro R S hRS ω
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hRS))

lemma nu_trunc_tendsto (hσ : IsIIDNonneg P σ) :
    Tendsto (fun R : ℕ => nu P (trunc σ R)) atTop (𝓝 (nu P σ)) := by
  rw [← nu_trunc_iSup hσ]
  exact tendsto_atTop_iSup nu_trunc_mono

end SolomonRWRE.DiffEq.Proof
-- End Truncation

-- Begin BoundedBlockAverage

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {σ : ℕ → Ω → ℝ}

lemma bounded_block_average (hσ : IsIIDNonneg P σ) {B : ℝ}
    (hb : ∀ i ω, σ (i+1) ω ≤ B) (k : ℕ) (hk : 0 < k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (∑ j ∈ range n, block (fun i => σ (i+1) ω) j k) / n) atTop
        (𝓝 ((∫ ω, σ 1 ω ∂P)^k)) := by
  have hr : ∀ᵐ ω ∂P, ∀ r : ℕ, Tendsto (fun n : ℕ =>
      (∑ q ∈ range n, block (fun i => σ (i+1) ω) (k*q+r) k) / n) atTop
        (𝓝 ((∫ ω, σ 1 ω ∂P)^k)) := by
    apply ae_all_iff.mpr
    intro r
    exact residue_block_strongLaw hσ.meas hσ.nonneg hσ.indep hσ.ident hb k r
  filter_upwards [hr] with ω hω
  apply residue_average_limit hk (B := B^k)
  · intro n
    exact ⟨block_nonneg (fun i => hσ.nonneg i ω) n k,
      block_le_pow (fun i => hσ.nonneg i ω) (fun i => hb i ω) n k⟩
  · intro r _
    exact hω r

lemma trunc_mean_ofReal (hσ : IsIIDNonneg P σ) (R : ℕ) :
    ENNReal.ofReal (∫ ω, trunc σ R 1 ω ∂P) = nu P (trunc σ R) := by
  exact ofReal_integral_eq_lintegral_ofReal (trunc_integrable hσ R 0)
    (ae_of_all _ fun ω => (iid_trunc hσ R).nonneg 0 ω)

lemma trunc_block_average (hσ : IsIIDNonneg P σ) (R k : ℕ) (hk : 0 < k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      (∑ j ∈ range n, block (fun i => trunc σ R (i+1) ω) j k) / n) atTop
        (𝓝 ((∫ ω, trunc σ R 1 ω ∂P)^k)) :=
  bounded_block_average (iid_trunc hσ R) (fun i ω => trunc_bound R (i+1) ω) k hk

end SolomonRWRE.DiffEq.Proof
-- End BoundedBlockAverage

-- Begin TriangularSum

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

lemma Z_eq_blocks {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Z σ n ω = ∑ j ∈ range n, block (fun i => σ (i+1) ω) j (n-j) := by
  induction n with
  | zero => simp [Z]
  | succ n ih =>
    rw [Z, ih, sum_range_succ]
    have he : (∑ j ∈ range n, block (fun i => σ (i+1) ω) j (n+1-j)) =
        (∑ j ∈ range n, block (fun i => σ (i+1) ω) j (n-j)) * σ (n+1) ω := by
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt (mem_range.mp hj)
      rw [show n+1-j = (n-j)+1 by omega, block_succ]
      rw [show j+(n-j)=n by omega]
    rw [he, show n+1-n=1 by omega, block_one]
    ring

lemma triangle_succ (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range (n+1), ∑ k ∈ range (n+1-j), f j (k+1)) =
      (∑ j ∈ range n, ∑ k ∈ range (n-j), f j (k+1)) +
        ∑ j ∈ range (n+1), f j (n+1-j) := by
  rw [sum_range_succ, sum_range_succ]
  simp only [Nat.add_sub_cancel_left, sum_range_one]
  have he : (∑ j ∈ range n, ∑ k ∈ range (n+1-j), f j (k+1)) =
      (∑ j ∈ range n, ∑ k ∈ range (n-j), f j (k+1)) +
        ∑ j ∈ range n, f j (n+1-j) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hjn := mem_range.mp hj
    rw [show n+1-j=(n-j)+1 by omega, sum_range_succ]
  rw [he]
  ring

lemma total_eq_forward_blocks {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ m ∈ Icc 1 n, Z σ m ω) =
      ∑ j ∈ range n, ∑ k ∈ range (n-j), block (fun i => σ (i+1) ω) j (k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n+1), ih, triangle_succ, Z_eq_blocks]

end SolomonRWRE.DiffEq.Proof
-- End TriangularSum

-- Begin RectangleLower

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

lemma rectangle_le_total {Ω : Type*} (σ τ : ℕ → Ω → ℝ)
    (ht : ∀ i ω, 0 ≤ τ (i+1) ω) (hle : ∀ i ω, τ (i+1) ω ≤ σ (i+1) ω)
    (n K : ℕ) (ω : Ω) :
    (∑ k ∈ range K, ∑ j ∈ range (n-K), block (fun i => τ (i+1) ω) j (k+1)) ≤
      ∑ m ∈ Icc 1 n, Z σ m ω := by
  rw [total_eq_forward_blocks, sum_comm]
  have hs : ∀ i, 0 ≤ σ (i+1) ω := fun i => (ht i ω).trans (hle i ω)
  calc
    _ ≤ ∑ j ∈ range (n-K), ∑ k ∈ range (n-j), block (fun i => σ (i+1) ω) j (k+1) := by
      apply sum_le_sum
      intro j hj
      have hjn := mem_range.mp hj
      calc
        _ ≤ ∑ k ∈ range K, block (fun i => σ (i+1) ω) j (k+1) := by
          apply sum_le_sum
          intro k _
          exact block_mono (fun i => ht i ω) (fun i => hle i ω) j (k+1)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
          (fun k _ _ => block_nonneg hs j (k+1))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le _ _))
      (fun j _ _ => sum_nonneg fun k _ => block_nonneg hs j (k+1))

lemma shortened_average_limit {w : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ j ∈ range n, w j)/(n:ℝ)) atTop (𝓝 L)) (K : ℕ) :
    Tendsto (fun n : ℕ => (∑ j ∈ range (n-K), w j)/(n:ℝ)) atTop (𝓝 L) := by
  have hs : Tendsto (fun n : ℕ => n-K) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (N+K)] with n hn
    omega
  have hr : Tendsto (fun n : ℕ => ((n-K:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat (K:ℝ))
    apply (show Tendsto (fun n : ℕ => 1-(K:ℝ)/(n:ℝ)) atTop (𝓝 1) by simpa using hh).congr'
    filter_upwards [eventually_gt_atTop K] with n hn
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Nat.cast_sub (Nat.le_of_lt hn)]
    field_simp
  have hh := (h.comp hs).mul hr
  apply (show Tendsto (fun n : ℕ =>
      ((∑ j ∈ range (n-K), w j)/((n-K:ℕ):ℝ))*(((n-K:ℕ):ℝ)/(n:ℝ)))
      atTop (𝓝 L) by simpa using hh).congr'
  filter_upwards [eventually_gt_atTop K] with n hn
  have hm0 : ((n-K:ℕ):ℝ) ≠ 0 := by exact_mod_cast (by omega : n-K ≠ 0)
  field_simp

end SolomonRWRE.DiffEq.Proof
-- End RectangleLower

-- Begin FiniteLower

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {σ : ℕ → Ω → ℝ}

lemma finite_truncated_lower (hσ : IsIIDNonneg P σ) (R K : ℕ) :
    ∀ᵐ ω ∂P, (∑ k ∈ range K, nu P (trunc σ R)^(k+1)) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z σ m ω)/(n:ℝ))) atTop := by
  have ha : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n : ℕ =>
      (∑ j ∈ range n, block (fun i => trunc σ R (i+1) ω) j (k+1))/(n:ℝ))
        atTop (𝓝 ((∫ ω, trunc σ R 1 ω ∂P)^(k+1))) := by
    apply ae_all_iff.mpr
    intro k
    exact trunc_block_average hσ R (k+1) (by omega)
  filter_upwards [ha] with ω hω
  let m : ℝ := ∫ ω, trunc σ R 1 ω ∂P
  have hm : 0 ≤ m := integral_nonneg fun ω => (iid_trunc hσ R).nonneg 0 ω
  have hs := tendsto_finsetSum (range K) (fun k _ => shortened_average_limit (hω k) K)
  have hs' : Tendsto (fun n : ℕ =>
      (∑ k ∈ range K, ∑ j ∈ range (n-K), block (fun i => trunc σ R (i+1) ω) j (k+1))/(n:ℝ))
      atTop (𝓝 (∑ k ∈ range K, m^(k+1))) := by
    simpa only [← sum_div] using hs
  have he := ENNReal.continuous_ofReal.tendsto _ |>.comp hs'
  have hval : ENNReal.ofReal (∑ k ∈ range K, m^(k+1)) =
      ∑ k ∈ range K, nu P (trunc σ R)^(k+1) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => pow_nonneg hm _)]
    apply sum_congr rfl
    intro k _
    rw [ENNReal.ofReal_pow hm, trunc_mean_ofReal hσ R]
  rw [hval] at he
  rw [← he.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right
      (rectangle_le_total σ (trunc σ R) (iid_trunc hσ R).nonneg
        (fun i ω => trunc_le R (i+1) ω) n K ω) (Nat.cast_nonneg n)))

end SolomonRWRE.DiffEq.Proof
-- End FiniteLower

-- Begin NativeLower

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace SolomonRWRE.DiffEq.Proof

lemma native_liminf_lower {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) :
    ∀ᵐ ω ∂P, (∑' k : ℕ, nu P σ^(k+1)) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z σ m ω)/(n:ℝ))) atTop := by
  have h : ∀ᵐ ω ∂P, ∀ R K : ℕ, (∑ k ∈ range K, nu P (trunc σ R)^(k+1)) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z σ m ω)/(n:ℝ))) atTop := by
    apply ae_all_iff.mpr
    intro R
    apply ae_all_iff.mpr
    intro K
    exact finite_truncated_lower hσ R K
  filter_upwards [h] with ω hω
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro K
  have ht : Tendsto (fun R : ℕ => ∑ k ∈ range K, nu P (trunc σ R)^(k+1)) atTop
      (𝓝 (∑ k ∈ range K, nu P σ^(k+1))) := by
    apply tendsto_finsetSum
    intro k _
    exact ENNReal.Tendsto.pow (nu_trunc_tendsto hσ)
  exact le_of_tendsto ht (Eventually.of_forall fun R => hω R K)

end SolomonRWRE.DiffEq.Proof
-- End NativeLower

-- Begin PathSpace

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace SolomonRWRE.DiffEq.Proof

abbrev PathSpace := ℕ → ℝ≥0

noncomputable def pathMeasure (ρ : Measure ℝ≥0) : Measure PathSpace :=
  Measure.infinitePi (fun _ : ℕ => ρ)

instance pathMeasure_probability (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (pathMeasure ρ) := by
  unfold pathMeasure
  infer_instance

def pathShift (x : PathSpace) : PathSpace := fun n => x (n + 1)

lemma pathShift_measurable : Measurable pathShift := by
  unfold pathShift
  fun_prop

lemma pathShift_preserving (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    MeasurePreserving pathShift (pathMeasure ρ) (pathMeasure ρ) := by
  refine ⟨pathShift_measurable, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj Nat.succ_injective

lemma pathShift_iterate (n : ℕ) (x : PathSpace) (i : ℕ) :
    (pathShift^[n]) x i = x (i + n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (pathShift^[n]) x (i + 1) = _
    rw [ih]
    congr 1
    omega

def pathSigma (n : ℕ) (x : PathSpace) : ℝ := x (n - 1)

lemma pathSigma_succ (n : ℕ) (x : PathSpace) : pathSigma (n + 1) x = x n := by
  simp [pathSigma]

lemma path_eval_map (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (i : ℕ) :
    (pathMeasure ρ).map (fun x => x i) = ρ := by
  exact Measure.infinitePi_map_eval _ _

lemma pathSigma_iid (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    IsIIDNonneg (pathMeasure ρ) pathSigma := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact measurable_coe_nnreal_real.comp (measurable_pi_apply n)
  · intro n x
    exact NNReal.coe_nonneg _
  · exact iIndepFun_infinitePi (X := fun _ (x : ℝ≥0) => (x : ℝ)) (by fun_prop)
  · intro n
    refine ⟨(measurable_coe_nnreal_real.comp (measurable_pi_apply n)).aemeasurable,
      (measurable_coe_nnreal_real.comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
    change (pathMeasure ρ).map ((fun y : ℝ≥0 => (y : ℝ)) ∘ (fun x => x n)) =
      (pathMeasure ρ).map ((fun y : ℝ≥0 => (y : ℝ)) ∘ (fun x => x 0))
    rw [← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), path_eval_map, path_eval_map]

noncomputable def marginalMean (ρ : Measure ℝ≥0) : ℝ≥0∞ := ∫⁻ x, (x : ℝ≥0∞) ∂ρ

lemma pathSigma_mean (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    nu (pathMeasure ρ) pathSigma = marginalMean ρ := by
  unfold nu marginalMean
  simp only [pathSigma, Nat.sub_self, ENNReal.ofReal_coe_nnreal]
  rw [← lintegral_map (by fun_prop) (by fun_prop), path_eval_map]

end SolomonRWRE.DiffEq.Proof
-- End PathSpace

-- Begin TrajectoryLaw

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace SolomonRWRE.DiffEq.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {σ : ℕ → Ω → ℝ}

def trajectory (σ : ℕ → Ω → ℝ) (ω : Ω) : PathSpace :=
  fun i => Real.toNNReal (σ (i + 1) ω)

lemma trajectory_measurable (hσ : IsIIDNonneg P σ) : Measurable (trajectory σ) := by
  exact measurable_pi_lambda _ fun i => (hσ.meas i).real_toNNReal

lemma trajectory_coe (hσ : IsIIDNonneg P σ) (ω : Ω) (i : ℕ) :
    (trajectory σ ω i : ℝ) = σ (i + 1) ω := Real.coe_toNNReal _ (hσ.nonneg i ω)

noncomputable def trajectoryMarginal (P : Measure Ω) (σ : ℕ → Ω → ℝ) : Measure ℝ≥0 :=
  P.map (fun ω => Real.toNNReal (σ 1 ω))

lemma trajectoryMarginal_probability [IsProbabilityMeasure P] (hσ : IsIIDNonneg P σ) :
    IsProbabilityMeasure (trajectoryMarginal P σ) :=
  Measure.isProbabilityMeasure_map (hσ.meas 0).real_toNNReal.aemeasurable

lemma trajectory_map (hσ : IsIIDNonneg P σ) :
    P.map (trajectory σ) = pathMeasure (trajectoryMarginal P σ) := by
  have hi := hσ.indep.comp (fun _ => Real.toNNReal) (fun _ => measurable_real_toNNReal)
  rw [show trajectory σ = (fun ω i => Real.toNNReal (σ (i + 1) ω)) from rfl,
    hi.map_fun_eq_infinitePi_map (fun i => (hσ.meas i).real_toNNReal)]
  unfold pathMeasure trajectoryMarginal
  congr 1
  funext i
  exact ((hσ.ident i).comp measurable_real_toNNReal).map_eq

lemma trajectory_mean (hσ : IsIIDNonneg P σ) :
    marginalMean (trajectoryMarginal P σ) = nu P σ := by
  unfold marginalMean trajectoryMarginal nu
  rw [lintegral_map (by fun_prop) (hσ.meas 0).real_toNNReal]
  rfl

lemma trajectory_Z (hσ : IsIIDNonneg P σ) (n : ℕ) (ω : Ω) :
    Z pathSigma n (trajectory σ ω) = Z σ n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Z, pathSigma_succ, trajectory_coe hσ, ih]

end SolomonRWRE.DiffEq.Proof
-- End TrajectoryLaw

-- Begin Perpetuity

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace SolomonRWRE.DiffEq.Proof

noncomputable def forwardPerpetuity (x : PathSpace) : ℝ≥0∞ :=
  ∑' k : ℕ, ∏ i ∈ Finset.range (k + 1), (x i : ℝ≥0∞)

lemma forwardPerpetuity_measurable : Measurable forwardPerpetuity := by
  unfold forwardPerpetuity
  exact Measurable.tsum fun k => by fun_prop

lemma path_product_mean (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (k : ℕ) :
    (∫⁻ x, ∏ i ∈ Finset.range k, (x i : ℝ≥0∞) ∂pathMeasure ρ) = marginalMean ρ ^ k := by
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun]
  · have h : ∀ i : ℕ, (∫⁻ x : PathSpace, (x i : ℝ≥0∞) ∂pathMeasure ρ) = marginalMean ρ := by
      intro i
      unfold marginalMean
      rw [← lintegral_map (by fun_prop) (by fun_prop), path_eval_map]
    simp only [h, Finset.prod_const, Finset.card_range]
  · exact iIndepFun_infinitePi (X := fun _ (x : ℝ≥0) => (x : ℝ≥0∞)) (by fun_prop)
  · intro i
    fun_prop

lemma forwardPerpetuity_lintegral (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    (∫⁻ x, forwardPerpetuity x ∂pathMeasure ρ) = marginalMean ρ / (1 - marginalMean ρ) := by
  unfold forwardPerpetuity
  rw [lintegral_tsum (fun k => (show Measurable (fun x : PathSpace => ∏ i ∈ Finset.range (k + 1), (x i : ℝ≥0∞)) from by fun_prop).aemeasurable)]
  simp_rw [path_product_mean]
  exact ENNReal.tsum_geometric_add_one _

lemma mean_ratio_ne_top {ρ : Measure ℝ≥0} (h : marginalMean ρ < 1) :
    marginalMean ρ / (1 - marginalMean ρ) ≠ ⊤ := by
  apply ENNReal.div_ne_top
  · exact ne_top_of_lt h
  · exact (tsub_pos_of_lt h).ne'

lemma forwardPerpetuity_finite (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (h : marginalMean ρ < 1) : ∀ᵐ x ∂pathMeasure ρ, forwardPerpetuity x < ⊤ := by
  apply ae_lt_top forwardPerpetuity_measurable
  rw [forwardPerpetuity_lintegral]
  exact mean_ratio_ne_top h

lemma forwardPerpetuity_integrable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (h : marginalMean ρ < 1) : Integrable (fun x => (forwardPerpetuity x).toReal) (pathMeasure ρ) := by
  apply integrable_toReal_of_lintegral_ne_top forwardPerpetuity_measurable.aemeasurable
  rw [forwardPerpetuity_lintegral]
  exact mean_ratio_ne_top h

lemma forwardPerpetuity_integral (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (h : marginalMean ρ < 1) :
    (∫ x, (forwardPerpetuity x).toReal ∂pathMeasure ρ) =
      (marginalMean ρ / (1 - marginalMean ρ)).toReal := by
  rw [integral_toReal forwardPerpetuity_measurable.aemeasurable (forwardPerpetuity_finite ρ h),
    forwardPerpetuity_lintegral]

lemma forwardPerpetuity_all_shifts_finite (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (h : marginalMean ρ < 1) :
    ∀ᵐ x ∂pathMeasure ρ, ∀ j : ℕ, forwardPerpetuity ((pathShift^[j]) x) < ⊤ := by
  rw [ae_all_iff]
  intro j
  exact ((pathShift_preserving ρ).iterate j).quasiMeasurePreserving.ae (forwardPerpetuity_finite ρ h)

end SolomonRWRE.DiffEq.Proof
-- End Perpetuity

-- Begin MaximalSums

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

noncomputable def ergodicAverage (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * birkhoffSum T f n ω

noncomputable def runningMax (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => max 0 (f ω + runningMax T f n (T ω))

lemma runningMax_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ runningMax T f n ω := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma runningMax_mono (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    Monotone (fun n => runningMax T f n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing ω with
  | zero => exact runningMax_nonneg T f 1 ω
  | succ n ih =>
    apply max_le_max le_rfl
    linarith [ih (T ω)]

lemma runningMax_attained (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∃ k ≤ n, runningMax T f n ω = birkhoffSum T f k ω := by
  induction n generalizing ω with
  | zero => exact ⟨0,le_rfl,rfl⟩
  | succ n ih =>
    obtain ⟨k,hk,he⟩ := ih (T ω)
    by_cases h : f ω + runningMax T f n (T ω) ≤ 0
    · exact ⟨0,by omega,by simp only [runningMax,max_eq_left h,birkhoffSum_zero]⟩
    · refine ⟨k+1,by omega,?_⟩
      rw [runningMax,max_eq_right (le_of_not_ge h),birkhoffSum_succ',he]

lemma sum_le_runningMax (T : Ω → Ω) (f : Ω → ℝ) {k n : ℕ} (hkn : k ≤ n) (ω : Ω) :
    birkhoffSum T f k ω ≤ runningMax T f n ω := by
  induction n generalizing k ω with
  | zero =>
    have hk : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    cases k with
    | zero => simpa only [birkhoffSum_zero] using runningMax_nonneg T f (n+1) ω
    | succ k =>
      rw [birkhoffSum_succ',runningMax]
      have hh := ih (k := k) (by omega) (T ω)
      linarith [le_max_right (0 : ℝ) (f ω + runningMax T f n (T ω))]

lemma runningMax_pos_iff (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 < runningMax T f n ω ↔ ∃ k ≤ n, 0 < birkhoffSum T f k ω := by
  constructor
  · intro h
    obtain ⟨k,hk,he⟩ := runningMax_attained T f n ω
    exact ⟨k,hk,he ▸ h⟩
  · rintro ⟨k,hk,hpos⟩
    exact hpos.trans_le (sum_le_runningMax T f hk ω)

lemma runningMax_indicator_lower (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    runningMax T f (n+1) ω - runningMax T f n (T ω) ≤
      {x | 0 < runningMax T f (n+1) x}.indicator f ω := by
  classical
  by_cases h : 0 < runningMax T f (n+1) ω
  · rw [Set.indicator_of_mem (show ω ∈ {x | 0 < runningMax T f (n+1) x} from h)]
    have hp : 0 < f ω + runningMax T f n (T ω) := by
      simpa only [runningMax,lt_max_iff,lt_self_iff_false,false_or] using h
    rw [runningMax,max_eq_right hp.le]
    linarith
  · rw [Set.indicator_of_notMem (show ω ∉ {x | 0 < runningMax T f (n+1) x} from h)]
    have hz : runningMax T f (n+1) ω = 0 := le_antisymm (le_of_not_gt h) (runningMax_nonneg T f _ ω)
    rw [hz]
    linarith [runningMax_nonneg T f n (T ω)]

end KingmanSubadditive.Ergodic.Proof
-- End MaximalSums

-- Begin HopfFinite

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

lemma integral_preserving (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Measurable f) :
    (∫ ω, f (T ω) ∂μ) = ∫ ω,f ω ∂μ := by
  have he := integral_map hT.measurable.aemeasurable
    (hf.aestronglyMeasurable : AEStronglyMeasurable f (Measure.map T μ))
  rw [hT.map_eq] at he
  exact he.symm

lemma runningMax_measurable (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (runningMax T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

lemma runningMax_integrable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (n : ℕ) : Integrable (runningMax T f n) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih => exact (integrable_zero _ _ _).sup (hf.add (hT.integrable_comp_of_integrable ih))

lemma hopf_finite (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 < runningMax T f n ω}, f ω ∂μ := by
  cases n with
  | zero => simp [runningMax]
  | succ n =>
    have hm : MeasurableSet {ω | 0 < runningMax T f (n+1) ω} :=
      measurableSet_lt measurable_const (runningMax_measurable hT.measurable hf _)
    have h0 := runningMax_integrable hT hi n
    have h1 := runningMax_integrable hT hi (n+1)
    have hb := integral_mono (h1.sub (hT.integrable_comp_of_integrable h0)) (hi.indicator hm)
      (runningMax_indicator_lower T f n)
    simp only [Pi.sub_apply,Function.comp_def] at hb
    have hc : Integrable (fun ω => runningMax T f n (T ω)) μ := hT.integrable_comp_of_integrable h0
    rw [integral_sub h1 hc,
      integral_preserving hT (runningMax_measurable hT.measurable hf n),integral_indicator hm] at hb
    have hm' := integral_mono h0 h1 (fun ω => runningMax_mono T f ω (Nat.le_succ n))
    linarith

end KingmanSubadditive.Ergodic.Proof
-- End HopfFinite

-- Begin HopfMaximal

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

def maximalEvent (T : Ω → Ω) (f : Ω → ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < birkhoffSum T f n ω}

lemma sum_measurable (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  unfold birkhoffSum
  fun_prop

lemma maximalEvent_measurable (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) :
    MeasurableSet (maximalEvent T f) := by
  change MeasurableSet {ω | ∃ n : ℕ, 0 < birkhoffSum T f n ω}
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_lt measurable_const (sum_measurable hT hf n))

omit [MeasurableSpace Ω] in
lemma maximal_indicator_tendsto (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    Tendsto (fun n => {x | 0 < runningMax T f n x}.indicator f ω) atTop
      (𝓝 ((maximalEvent T f).indicator f ω)) := by
  classical
  by_cases h : ω ∈ maximalEvent T f
  · obtain ⟨k,hk⟩ := h
    rw [Set.indicator_of_mem (show ω ∈ maximalEvent T f from ⟨k,hk⟩)]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (Set.indicator_of_mem (show ω ∈ {x | 0 < runningMax T f n x} from
      hk.trans_le (sum_le_runningMax T f hn ω)) f).symm
  · rw [Set.indicator_of_notMem h]
    have he (n : ℕ) : ω ∉ {x | 0 < runningMax T f n x} := by
      intro hp
      obtain ⟨k,_,hk⟩ := (runningMax_pos_iff T f n ω).mp hp
      exact h ⟨k,hk⟩
    simpa only [Set.indicator_of_notMem (he _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

lemma hopf_maximal (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    0 ≤ ∫ ω in maximalEvent T f, f ω ∂μ := by
  have hm n : MeasurableSet {ω | 0 < runningMax T f n ω} :=
    measurableSet_lt measurable_const (runningMax_measurable hT.measurable hf n)
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun ω => ‖f ω‖)
    (fun n => hf.aestronglyMeasurable.indicator (hm n)) hi.norm
    (fun n => ae_of_all _ (fun ω => norm_indicator_le_norm_self _ _))
    (ae_of_all _ (maximal_indicator_tendsto T f))
  simp only [integral_indicator (hm _),integral_indicator (maximalEvent_measurable hT.measurable hf)] at ht
  exact ge_of_tendsto ht (Eventually.of_forall (hopf_finite hT hf hi))

end KingmanSubadditive.Ergodic.Proof
-- End HopfMaximal

-- Begin BoundedSequenceLimits

open Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

lemma limsup_le_limsup_error {u v e : ℕ → ℝ}
    (hu : atTop.IsCoboundedUnder (· ≤ ·) u)
    (hv : atTop.IsBoundedUnder (· ≤ ·) v)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ n in atTop, u n ≤ v n + e n) :
    limsup u atTop ≤ limsup v atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hf := frequently_lt_of_lt_limsup hu (show limsup u atTop - ε/2 < limsup u atTop by linarith)
  have he' := he.eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity))
  have hb : limsup u atTop - ε ≤ limsup v atTop := by
    apply le_limsup_of_frequently_le _ hv
    exact ((hf.and_eventually he').and_eventually h).mono fun n hn => by
      linarith [hn.1.1,hn.1.2,hn.2]
  linarith

lemma limsup_eq_of_sub_tendsto_zero {u v : ℕ → ℝ}
    (hul : BddBelow (Set.range u)) (huu : BddAbove (Set.range u))
    (hvl : BddBelow (Set.range v)) (hvu : BddAbove (Set.range v))
    (he : Tendsto (fun n => u n-v n) atTop (𝓝 0)) :
    limsup u atTop = limsup v atTop := by
  apply le_antisymm
  · exact limsup_le_limsup_error hul.isBoundedUnder_of_range.isCobounded_le
      hvu.isBoundedUnder_of_range he (Eventually.of_forall fun n => by linarith)
  · have he' : Tendsto (fun n => v n-u n) atTop (𝓝 0) := by
      simpa only [neg_sub, neg_zero] using he.neg
    exact limsup_le_limsup_error hvl.isBoundedUnder_of_range.isCobounded_le
      huu.isBoundedUnder_of_range he' (Eventually.of_forall fun n => by linarith)

end KingmanSubadditive.Ergodic.Proof
-- End BoundedSequenceLimits

-- Begin ErgodicAverageBasic

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

lemma average_measurable (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (ergodicAverage T f n) := by
  exact measurable_const.mul (sum_measurable hT hf n)

lemma sum_integrable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (n : ℕ) : Integrable (birkhoffSum T f n) μ := by
  unfold birkhoffSum
  exact integrable_finsetSum _ fun i _ => (hT.iterate i).integrable_comp_of_integrable hf

lemma average_integrable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (n : ℕ) : Integrable (ergodicAverage T f n) μ :=
  (sum_integrable hT hf n).const_mul _

omit [MeasurableSpace Ω] in
lemma average_abs_bound (T : Ω → Ω) {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (n : ℕ) (ω : Ω) : |ergodicAverage T f n ω| ≤ B := by
  by_cases hn : n=0
  · simp [hn,ergodicAverage,hB]
  have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : |birkhoffSum T f n ω| ≤ (n:ℝ)*B := by
    unfold birkhoffSum
    calc
      _ ≤ ∑ i ∈ Finset.range n, |f (T^[i] ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, B := Finset.sum_le_sum fun i _ => hf _
      _ = _ := by simp
  rw [ergodicAverage,abs_mul,abs_inv,abs_of_pos hn']
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn'.le)).trans_eq (by field_simp)

omit [MeasurableSpace Ω] in
lemma average_shift_tendsto {f : Ω → ℝ} {B : ℝ} (hf : ∀ ω, |f ω| ≤ B)
    (T : Ω → Ω) (ω : Ω) :
    Tendsto (fun n => ergodicAverage T f n (T ω)-ergodicAverage T f n ω) atTop (𝓝 0) := by
  have hb : Bornology.IsBounded (Set.range f) := Metric.isBounded_range_iff.mpr ⟨2*B,by
    intro x y
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [hf x,hf y])⟩
  simpa only [ergodicAverage,birkhoffAverage,smul_eq_mul] using
    tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ hb T ω

lemma integral_average (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {n : ℕ} (hn : n ≠ 0) :
    (∫ ω,ergodicAverage T f n ω ∂μ) = ∫ ω,f ω ∂μ := by
  unfold ergodicAverage birkhoffSum
  have hc (i : ℕ) : Integrable (fun ω => f (T^[i] ω)) μ :=
    (hT.iterate i).integrable_comp_of_integrable hi
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => hc i)]
  simp only [integral_preserving (hT.iterate _) hf,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
  field_simp

end KingmanSubadditive.Ergodic.Proof
-- End ErgodicAverageBasic

-- Begin PerpetuityDomination

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace SolomonRWRE.DiffEq.Proof

lemma block_ofReal (x : PathSpace) (j k : ℕ) :
    ENNReal.ofReal (block (fun i => (x i : ℝ)) j k) =
      ∏ i ∈ range k, (x (j + i) : ℝ≥0∞) := by
  unfold block
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => NNReal.coe_nonneg _)]
  simp only [ENNReal.ofReal_coe_nnreal]

lemma partial_blocks_le_perpetuity (x : PathSpace) (j n : ℕ) :
    ENNReal.ofReal (∑ k ∈ range n, block (fun i => (x i : ℝ)) j (k + 1)) ≤
      forwardPerpetuity ((pathShift^[j]) x) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => block_nonneg (fun i => NNReal.coe_nonneg _) _ _)]
  simp only [block_ofReal, forwardPerpetuity, pathShift_iterate, Nat.add_comm]
  exact ENNReal.sum_le_tsum _

lemma total_le_perpetuity_sum (x : PathSpace) (n : ℕ)
    (hfinite : ∀ j, forwardPerpetuity ((pathShift^[j]) x) < ⊤) :
    (∑ m ∈ Icc 1 n, Z pathSigma m x) ≤
      ∑ j ∈ range n, (forwardPerpetuity ((pathShift^[j]) x)).toReal := by
  rw [total_eq_forward_blocks]
  change (∑ j ∈ range n, ∑ k ∈ range (n-j), block (fun i => (x i : ℝ)) j (k+1)) ≤ _
  apply sum_le_sum
  intro j _
  have h := ENNReal.toReal_mono (hfinite j).ne (partial_blocks_le_perpetuity x j (n-j))
  rw [ENNReal.toReal_ofReal (sum_nonneg (fun k _ => block_nonneg (fun i => NNReal.coe_nonneg _) _ _))] at h
  exact h

lemma average_le_perpetuity_average (x : PathSpace) (n : ℕ)
    (hfinite : ∀ j, forwardPerpetuity ((pathShift^[j]) x) < ⊤) :
    (∑ m ∈ Icc 1 n, Z pathSigma m x) / n ≤
      KingmanSubadditive.Ergodic.Proof.ergodicAverage pathShift
        (fun y => (forwardPerpetuity y).toReal) n x := by
  unfold KingmanSubadditive.Ergodic.Proof.ergodicAverage
    birkhoffSum
  rw [div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_left (total_le_perpetuity_sum x n hfinite)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

end SolomonRWRE.DiffEq.Proof
-- End PerpetuityDomination

-- Begin BoundedAverageLimits

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

noncomputable def upperAverage (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  limsup (fun n => ergodicAverage T f n ω) atTop

lemma average_range_bounds (T : Ω → Ω) {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (ω : Ω) :
    BddBelow (Set.range (fun n => ergodicAverage T f n ω)) ∧
    BddAbove (Set.range (fun n => ergodicAverage T f n ω)) := by
  constructor
  · exact ⟨-B,by rintro _ ⟨n,rfl⟩; exact (abs_le.mp (average_abs_bound T hB hf n ω)).1⟩
  · exact ⟨B,by rintro _ ⟨n,rfl⟩; exact (abs_le.mp (average_abs_bound T hB hf n ω)).2⟩

lemma upperAverage_bound (T : Ω → Ω) {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (ω : Ω) : |upperAverage T f ω| ≤ B := by
  obtain ⟨hl,hu⟩ := average_range_bounds T hB hf ω
  apply abs_le.mpr
  constructor
  · exact le_limsup_of_frequently_le (Frequently.of_forall fun n =>
      (abs_le.mp (average_abs_bound T hB hf n ω)).1) hu.isBoundedUnder_of_range
  · exact limsup_le_of_le hl.isBoundedUnder_of_range.isCobounded_le
      (Eventually.of_forall fun n => (abs_le.mp (average_abs_bound T hB hf n ω)).2)

lemma upperAverage_invariant (T : Ω → Ω) {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (ω : Ω) : upperAverage T f (T ω)=upperAverage T f ω := by
  obtain ⟨hl,hu⟩ := average_range_bounds T hB hf ω
  obtain ⟨hl',hu'⟩ := average_range_bounds T hB hf (T ω)
  exact limsup_eq_of_sub_tendsto_zero hl' hu' hl hu (average_shift_tendsto hf T ω)

lemma upperAverage_measurable [MeasurableSpace Ω] {T : Ω → Ω} (hT : Measurable T)
    {f : Ω → ℝ} (hf : Measurable f) : Measurable (upperAverage T f) :=
  Measurable.limsup fun n => average_measurable hT hf n

lemma upperAverage_integrable [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω, |f ω| ≤ B) : Integrable (upperAverage T f) μ := by
  apply Integrable.mono' (integrable_const B) (upperAverage_measurable hT hf).aestronglyMeasurable
  exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using upperAverage_bound T hB hb ω

end KingmanSubadditive.Ergodic.Proof
-- End BoundedAverageLimits

-- Begin HopfInvariantComparison

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

lemma average_sub_invariant {T : Ω → Ω} (f g : Ω → ℝ)
    (hg : ∀ ω, g (T ω)=g ω) {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    ergodicAverage T (fun x => f x-g x) n ω = ergodicAverage T f n ω-g ω := by
  have hs := congrFun (birkhoffSum_of_comp_eq (show g ∘ T=g from funext hg) n) ω
  simp only [Pi.smul_apply,nsmul_eq_mul] at hs
  have he : birkhoffSum T (fun x => f x-g x) n ω = birkhoffSum T f n ω-birkhoffSum T g n ω :=
    birkhoffSum_sub T f g n ω
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
  rw [ergodicAverage,he,hs,ergodicAverage]
  field_simp

lemma maximalEvent_upper_sub_eps {T : Ω → Ω} {f : Ω → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ ω, |f ω| ≤ B) {ε : ℝ} (hε : 0<ε) :
    maximalEvent T (fun x => f x-(upperAverage T f x-ε))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  obtain ⟨hl,_⟩ := average_range_bounds T hB hf ω
  have hh := frequently_lt_of_lt_limsup hl.isBoundedUnder_of_range.isCobounded_le
    (show upperAverage T f ω-ε < upperAverage T f ω by linarith)
  obtain ⟨n,hn,hpos⟩ := (hh.and_eventually (eventually_gt_atTop 0)).exists
  have hn0 : n≠0 := Nat.ne_of_gt hpos
  have hn' : (0:ℝ)<n := by exact_mod_cast hpos
  have ha := average_sub_invariant f (fun x=>upperAverage T f x-ε)
    (fun x=>by rw [upperAverage_invariant T hB hf x]) hn0 ω
  have hp : 0<ergodicAverage T (fun x=>f x-(upperAverage T f x-ε)) n ω := by linarith
  exact ⟨n,(mul_pos_iff.mp hp).resolve_right (by intro h; exact (inv_pos.mpr hn').not_gt h.1) |>.2⟩

lemma integral_upperAverage_le [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω, |f ω| ≤ B) : (∫ ω,upperAverage T f ω ∂μ) ≤ ∫ ω,f ω ∂μ := by
  have hm := upperAverage_measurable hT.measurable hf
  have hu := upperAverage_integrable hT.measurable hf hB hb (μ:=μ)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hh := hopf_maximal hT (hf.sub (hm.sub measurable_const))
    (hi.sub (hu.sub (integrable_const ε)))
  change 0 ≤ ∫ ω in maximalEvent T (fun x=> f x-(upperAverage T f x-ε)), f ω-(upperAverage T f ω-ε) ∂μ at hh
  rw [maximalEvent_upper_sub_eps hB hb hε,Measure.restrict_univ] at hh
  have hc : Integrable (fun ω=>upperAverage T f ω-ε) μ := hu.sub (integrable_const ε)
  rw [integral_sub hi hc,integral_sub hu (integrable_const ε)] at hh
  simp only [integral_const] at hh
  simp at hh
  linarith

end KingmanSubadditive.Ergodic.Proof
-- End HopfInvariantComparison

-- Begin BoundedAverageConvergence

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

lemma real_limsup_neg {u : ℕ → ℝ} (hl : BddBelow (Set.range u))
    (hu : BddAbove (Set.range u)) : limsup (fun n => -u n) atTop = -liminf u atTop := by
  let e : ℝ ≃o ℝᵒᵈ := { toEquiv := Equiv.neg ℝ, map_rel_iff' := by intro a b; exact neg_le_neg_iff }
  have hl' : BddBelow (Set.range (fun n => e (u n))) := by
    obtain ⟨b,hb⟩ := hl
    exact ⟨-b,by rintro _ ⟨n,rfl⟩; change -u n ≤ -b; exact neg_le_neg (hb ⟨n,rfl⟩)⟩
  have hu' : BddAbove (Set.range (fun n => e (u n))) := by
    obtain ⟨b,hb⟩ := hu
    exact ⟨-b,by rintro _ ⟨n,rfl⟩; change -b ≤ -u n; exact neg_le_neg (hb ⟨n,rfl⟩)⟩
  exact (e.liminf_apply hl.isBoundedUnder_of_range hu.isBoundedUnder_of_range.isCobounded_ge
    hl'.isBoundedUnder_of_range hu'.isBoundedUnder_of_range.isCobounded_ge).symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

omit [MeasurableSpace Ω] in
lemma upperAverage_neg {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (ω : Ω) :
    upperAverage T (fun x=>-f x) ω = -liminf (fun n=>ergodicAverage T f n ω) atTop := by
  obtain ⟨hl,hu⟩ := average_range_bounds T hB hf ω
  have he (n : ℕ) : ergodicAverage T (fun x=>-f x) n ω = -ergodicAverage T f n ω := by
    simp [ergodicAverage,birkhoffSum,Finset.sum_neg_distrib]
  simp only [upperAverage,he]
  exact real_limsup_neg hl hu

lemma bounded_average_ae_converges (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω, |f ω| ≤ B) :
    ∀ᵐ ω ∂μ, Tendsto (fun n=>ergodicAverage T f n ω) atTop (𝓝 (upperAverage T f ω)) := by
  have hbn : ∀ ω, |(-f ω)|≤B := by intro ω; simpa using hb ω
  have hu := upperAverage_integrable hT.measurable hf hB hb (μ:=μ)
  have hv := upperAverage_integrable hT.measurable hf.neg hB hbn (μ:=μ)
  change Integrable (upperAverage T (fun x=>-f x)) μ at hv
  have hp (ω : Ω) : 0 ≤ upperAverage T f ω+upperAverage T (fun x=>-f x) ω := by
    rw [upperAverage_neg hB hb ω]
    obtain ⟨hl,hh⟩ := average_range_bounds T hB hb ω
    exact sub_nonneg.mpr (liminf_le_limsup hh.isBoundedUnder_of_range hl.isBoundedUnder_of_range)
  have he : (∫ ω,upperAverage T f ω+upperAverage T (fun x=>-f x) ω ∂μ)=0 := by
    apply le_antisymm
    · rw [integral_add hu hv]
      have h1 := integral_upperAverage_le hT hf hi hB hb
      have h2 := integral_upperAverage_le hT hf.neg hi.neg hB hbn
      change (∫ ω,upperAverage T (fun x=>-f x) ω ∂μ) ≤ ∫ ω,-f ω ∂μ at h2
      rw [integral_neg] at h2
      linarith
    · exact integral_nonneg hp
  have hz := (integral_eq_zero_iff_of_nonneg hp (hu.add hv)).mp he
  filter_upwards [hz] with ω hω
  rw [upperAverage_neg hB hb ω] at hω
  simp only [Pi.zero_apply] at hω
  obtain ⟨hl,hh⟩ := average_range_bounds T hB hb ω
  apply tendsto_of_liminf_eq_limsup (show liminf (fun n=>ergodicAverage T f n ω) atTop = upperAverage T f ω by linarith) rfl
    hh.isBoundedUnder_of_range hl.isBoundedUnder_of_range

end KingmanSubadditive.Ergodic.Proof
-- End BoundedAverageConvergence

-- Begin BoundedBirkhoff

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma bounded_birkhoff_convergence (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω, |f ω| ≤ B) :
    ∃ ξ : Ω → ℝ, Measurable ξ ∧ Integrable ξ μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n=>ergodicAverage T f n ω) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun n=>∫ ω,|ergodicAverage T f n ω-ξ ω| ∂μ) atTop (𝓝 0) ∧
      (∫ ω,ξ ω ∂μ) = ∫ ω,f ω ∂μ := by
  have hm := upperAverage_measurable hT.measurable hf
  have hu := upperAverage_integrable hT.measurable hf hB hb (μ:=μ)
  have ha := bounded_average_ae_converges hT hf hi hB hb
  refine ⟨upperAverage T f,hm,hu,ha,?_,?_⟩
  · have hd := tendsto_integral_of_dominated_convergence (μ:=μ) (fun _ : Ω => 2*B)
      (fun n => ((average_measurable hT.measurable hf n).sub hm).abs.aestronglyMeasurable)
      (integrable_const _)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs,abs_abs]
        exact (abs_sub _ _).trans (by linarith [average_abs_bound T hB hb n ω,upperAverage_bound T hB hb ω]))
      (ha.mono fun ω hω => by simpa using (hω.sub_const (upperAverage T f ω)).abs)
    simpa using hd
  · have hd := tendsto_integral_of_dominated_convergence (μ:=μ) (fun _ : Ω => B)
      (fun n => (average_measurable hT.measurable hf n).aestronglyMeasurable)
      (integrable_const _)
      (fun n => ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using average_abs_bound T hB hb n ω) ha
    have hc : Tendsto (fun n=>∫ ω,ergodicAverage T f n ω ∂μ) atTop (𝓝 (∫ ω,f ω ∂μ)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_gt_atTop 0] with n hn
        exact (integral_average hT hf hi (Nat.ne_of_gt hn)).symm)
    exact tendsto_nhds_unique hd hc

end KingmanSubadditive.Ergodic.Proof
-- End BoundedBirkhoff

-- Begin MaximalL1Bound

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

omit [MeasurableSpace Ω] in
lemma average_abs_le (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    |ergodicAverage T f n ω| ≤ ergodicAverage T (fun x=>|f x|) n ω := by
  unfold ergodicAverage birkhoffSum
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr (Nat.cast_nonneg n))

omit [MeasurableSpace Ω] in
lemma average_sub (T : Ω → Ω) (f g : Ω → ℝ) (n : ℕ) (ω : Ω) :
    ergodicAverage T (fun x=>f x-g x) n ω = ergodicAverage T f n ω-ergodicAverage T g n ω := by
  simp [ergodicAverage,birkhoffSum,Finset.sum_sub_distrib,mul_sub]

lemma maximalL1_bound (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {a : ℝ} (ha : 0<a) :
    μ {ω | ∃ n, a < |ergodicAverage T f n ω|} ≤ ENNReal.ofReal ((∫ ω,|f ω| ∂μ)/a) := by
  let E := maximalEvent T (fun ω=>|f ω|-a)
  have hm : MeasurableSet E := maximalEvent_measurable hT.measurable (hf.abs.sub measurable_const)
  have hh := hopf_maximal hT (hf.abs.sub measurable_const) (hi.abs.sub (integrable_const a))
  change 0 ≤ ∫ ω in E, |f ω|-a ∂μ at hh
  rw [integral_sub hi.abs.integrableOn (integrable_const a)] at hh
  simp only [setIntegral_const,smul_eq_mul] at hh
  have hb : (∫ ω in E, |f ω| ∂μ) ≤ ∫ ω,|f ω| ∂μ :=
    setIntegral_le_integral hi.abs (ae_of_all _ fun ω => abs_nonneg _) 
  have he : μ.real E ≤ (∫ ω,|f ω| ∂μ)/a := by
    rw [le_div_iff₀ ha]
    linarith
  apply le_trans (measure_mono ?_) ((ENNReal.toReal_le_toReal (measure_ne_top μ E) ENNReal.ofReal_ne_top).mp ?_)
  · intro ω hω
    obtain ⟨n,hn⟩ := hω
    have hn0 : n≠0 := by intro h; simp [h,ergodicAverage] at hn; linarith
    have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hs := average_sub_invariant (T:=T) (fun x=>|f x|) (fun _=>a) (fun _=>rfl) hn0 ω
    have hp : 0<ergodicAverage T (fun x=>|f x|-a) n ω := by
      linarith [average_abs_le T f n ω]
    exact ⟨n,(mul_pos_iff.mp hp).resolve_right (by intro h; exact (inv_pos.mpr hn').not_gt h.1) |>.2⟩
  · rw [ENNReal.toReal_ofReal (div_nonneg (integral_nonneg fun ω=>abs_nonneg _) ha.le)]
    exact he

end KingmanSubadditive.Ergodic.Proof
-- End MaximalL1Bound

-- Begin BoundedTruncation

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def boundedTruncation (f : Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ := max (-(N:ℝ)) (min (N:ℝ) (f ω))

lemma truncation_measurable {f : Ω → ℝ} (hf : Measurable f) (N : ℕ) :
    Measurable (boundedTruncation f N) := measurable_const.max (measurable_const.min hf)

lemma truncation_integrable {f : Ω → ℝ} (hf : Integrable f μ) (N : ℕ) :
    Integrable (boundedTruncation f N) μ := (integrable_const _).sup ((integrable_const _).inf hf)

omit [MeasurableSpace Ω] in
lemma truncation_abs_bound (f : Ω → ℝ) (N : ℕ) (ω : Ω) : |boundedTruncation f N ω|≤N := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith [Nat.cast_nonneg (α:=ℝ) N]) (min_le_left _ _)

omit [MeasurableSpace Ω] in
lemma truncation_error_bound (f : Ω → ℝ) (N : ℕ) (ω : Ω) :
    |f ω-boundedTruncation f N ω|≤|f ω| := by
  unfold boundedTruncation
  have hN : (0:ℝ)≤N := Nat.cast_nonneg _
  have hf := le_abs_self (f ω)
  have hf' := neg_abs_le (f ω)
  simp only [max_def,min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

omit [MeasurableSpace Ω] in
lemma truncation_tendsto (f : Ω → ℝ) (ω : Ω) :
    Tendsto (fun N=>boundedTruncation f N ω) atTop (𝓝 (f ω)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop |f ω|)] with N hN
  dsimp [boundedTruncation]
  rw [min_eq_right (le_abs_self _ |>.trans hN),max_eq_right (by linarith [neg_abs_le (f ω)])]

omit [IsProbabilityMeasure μ] in
lemma truncation_L1_tendsto {f : Ω → ℝ} (hf : Measurable f) (hi : Integrable f μ) :
    Tendsto (fun N=>∫ ω,|f ω-boundedTruncation f N ω| ∂μ) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (μ:=μ) (fun ω=>|f ω|)
    (fun N=>(hf.sub (truncation_measurable hf N)).abs.aestronglyMeasurable) hi.abs
    (fun N=>ae_of_all _ fun ω=>by simpa only [Real.norm_eq_abs,abs_abs,Pi.sub_apply] using truncation_error_bound f N ω)
    (ae_of_all _ fun ω=>by simpa using (tendsto_const_nhds.sub (truncation_tendsto f ω)).abs)
  simpa using ht

end KingmanSubadditive.Ergodic.Proof
-- End BoundedTruncation

-- Begin OscillationTransfer

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

def oscillationEvent (u : ℕ → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∀ N : ℕ, ∃ m≥N, ∃ n≥N, ε ≤ |u m ω-u n ω|}

lemma oscillation_subset (u v : ℕ → Ω → ℝ) (ξ : Ω → ℝ) {ε : ℝ} (hε : 0<ε) :
    oscillationEvent u ε ⊆ {ω | ¬ Tendsto (fun n=>v n ω) atTop (𝓝 (ξ ω))} ∪
      {ω | ∃ n, ε/4 < |u n ω-v n ω|} := by
  intro ω hω
  by_cases hv : Tendsto (fun n=>v n ω) atTop (𝓝 (ξ ω))
  · apply Or.inr
    by_contra he
    change ¬ ∃ n, ε/4 < |u n ω-v n ω| at he
    push Not at he
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hv.cauchySeq (ε/2) (by positivity)
    obtain ⟨m,hm,n,hn,hbig⟩ := hω N
    have hsmall := hN m hm n hn
    rw [Real.dist_eq] at hsmall
    have hh : |u m ω-u n ω| ≤ |u m ω-v m ω|+|v m ω-v n ω|+|u n ω-v n ω| := by
      calc
        _ = |(u m ω-v m ω)+(v m ω-v n ω)-(u n ω-v n ω)| := by congr 1; ring
        _ ≤ |(u m ω-v m ω)+(v m ω-v n ω)|+|u n ω-v n ω| := abs_sub ((u m ω-v m ω)+(v m ω-v n ω)) (u n ω-v n ω)
        _ ≤ _ := by linarith [abs_add_le (u m ω-v m ω) (v m ω-v n ω)]
    linarith [he m,he n]
  · exact Or.inl hv

lemma cauchy_of_not_oscillation (u : ℕ → ℝ)
    (h : ∀ k : ℕ, ¬ ∀ N : ℕ, ∃ m≥N, ∃ n≥N, (1:ℝ)/(k+1) ≤ |u m-u n|) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  have hh := h k
  push Not at hh
  obtain ⟨N,hN⟩ := hh
  exact ⟨N,fun m hm n hn => by rw [Real.dist_eq]; exact (hN m hm n hn).trans hk⟩

end KingmanSubadditive.Ergodic.Proof
-- End OscillationTransfer

-- Begin BirkhoffAECauchy

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma average_oscillation_null (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {ε : ℝ} (hε : 0<ε) :
    μ (oscillationEvent (ergodicAverage T f) ε)=0 := by
  have hb (N : ℕ) : μ (oscillationEvent (ergodicAverage T f) ε) ≤
      ENNReal.ofReal ((∫ ω,|f ω-boundedTruncation f N ω| ∂μ)/(ε/4)) := by
    obtain ⟨ξ,_,_,hξ,_,_⟩ := bounded_birkhoff_convergence hT
      (truncation_measurable hf N) (truncation_integrable hi N) (Nat.cast_nonneg N)
      (truncation_abs_bound f N)
    have hs := oscillation_subset (ergodicAverage T f)
      (ergodicAverage T (boundedTruncation f N)) ξ hε
    have hn : μ {ω | ¬ Tendsto (fun n=>ergodicAverage T (boundedTruncation f N) n ω) atTop (𝓝 (ξ ω))}=0 :=
      ae_iff.mp hξ
    have hm := maximalL1_bound hT (hf.sub (truncation_measurable hf N))
      (hi.sub (truncation_integrable hi N)) (show 0<ε/4 by positivity)
    change μ {ω | ∃ n, ε/4 < |ergodicAverage T (fun x=>f x-boundedTruncation f N x) n ω|} ≤ _ at hm
    simp only [average_sub,Pi.sub_apply] at hm
    exact (measure_mono hs).trans ((measure_union_le _ _).trans (by simpa only [hn,zero_add] using hm))
  have ht : Tendsto (fun N => ENNReal.ofReal ((∫ ω,|f ω-boundedTruncation f N ω| ∂μ)/(ε/4))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_div,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((truncation_L1_tendsto hf hi).div_const (ε/4))
  exact le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) (bot_le)

lemma birkhoff_ae_cauchy (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ ω ∂μ, CauchySeq (fun n=>ergodicAverage T f n ω) := by
  have hh (k : ℕ) : ∀ᵐ ω ∂μ, ω ∉ oscillationEvent (ergodicAverage T f) ((1:ℝ)/(k+1)) := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using average_oscillation_null hT hf hi (show (0:ℝ)<1/(k+1) by positivity)
  filter_upwards [ae_all_iff.mpr hh] with ω hω
  exact cauchy_of_not_oscillation _ hω

end KingmanSubadditive.Ergodic.Proof
-- End BirkhoffAECauchy

-- Begin AverageL1Contraction

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

lemma average_L1_bound (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) (n : ℕ) :
    (∫ ω,|ergodicAverage T f n ω| ∂μ) ≤ ∫ ω,|f ω| ∂μ := by
  by_cases hn : n=0
  · subst n
    simpa [ergodicAverage] using integral_nonneg (μ:=μ) (fun ω=>abs_nonneg (f ω))
  have h := integral_mono (average_integrable hT hi n).abs
    (average_integrable hT hi.abs n) (average_abs_le T f n)
  have he := integral_average hT hf.abs hi.abs hn
  change (∫ ω,ergodicAverage T (fun x=>|f x|) n ω ∂μ) = ∫ ω,|f ω| ∂μ at he
  exact h.trans_eq he

lemma average_L1_difference_bound (hT : MeasurePreserving T μ μ) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hi : Integrable f μ) (hj : Integrable g μ) (n : ℕ) :
    (∫ ω,|ergodicAverage T f n ω-ergodicAverage T g n ω| ∂μ) ≤ ∫ ω,|f ω-g ω| ∂μ := by
  have h := average_L1_bound hT (hf.sub hg) (hi.sub hj) n
  change (∫ ω,|ergodicAverage T (fun x=>f x-g x) n ω| ∂μ) ≤ ∫ ω,|f ω-g ω| ∂μ at h
  simpa only [average_sub] using h

end KingmanSubadditive.Ergodic.Proof
-- End AverageL1Contraction

-- Begin FatouL1Bound

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma fatou_L1_bound {u : ℕ → Ω → ℝ} {f : Ω → ℝ} {C : ℝ} (hC : 0≤C)
    (hu : ∀ n, Integrable (u n) μ) (hf : Measurable f)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n=>u n ω) atTop (𝓝 (f ω)))
    (hb : ∀ n, (∫ ω,|u n ω| ∂μ)≤C) : Integrable f μ ∧ (∫ ω,|f ω| ∂μ)≤C := by
  have he : (∫⁻ ω,‖f ω‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    have hlim : (∫⁻ ω,‖f ω‖ₑ ∂μ) = ∫⁻ ω,liminf (fun n=>‖u n ω‖ₑ) atTop ∂μ :=
      lintegral_congr_ae (ht.mono fun ω hω=>hω.enorm.liminf_eq.symm)
    rw [hlim]
    apply (lintegral_liminf_le' (fun n=>(hu n).aestronglyMeasurable.aemeasurable.enorm)).trans
    apply liminf_le_of_frequently_le' (Frequently.of_forall fun n=> ?_)
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hu n)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hb n)
  have hfi : Integrable f μ := ⟨hf.aestronglyMeasurable,he.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hfi,?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi] at he
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (by simpa only [Real.norm_eq_abs] using he)

end KingmanSubadditive.Ergodic.Proof
-- End FatouL1Bound

-- Begin BirkhoffLimit

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma birkhoff_ae_tendsto (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n=>ergodicAverage T f n ω) atTop (𝓝 (upperAverage T f ω)) := by
  filter_upwards [birkhoff_ae_cauchy hT hf hi] with ω hω
  obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete hω
  simpa only [upperAverage,hc.limsup_eq] using hc

lemma birkhoff_limit_integrable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) : Integrable (upperAverage T f) μ :=
  (fatou_L1_bound (integral_nonneg fun ω=>abs_nonneg (f ω))
    (average_integrable hT hi) (upperAverage_measurable hT.measurable hf)
    (birkhoff_ae_tendsto hT hf hi) (average_L1_bound hT hf hi)).1

lemma birkhoff_limit_L1_difference (hT : MeasurePreserving T μ μ) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hi : Integrable f μ) (hj : Integrable g μ) :
    (∫ ω,|upperAverage T f ω-upperAverage T g ω| ∂μ) ≤ ∫ ω,|f ω-g ω| ∂μ := by
  apply (fatou_L1_bound (integral_nonneg fun ω=>abs_nonneg (f ω-g ω))
    (fun n=>(average_integrable hT hi n).sub (average_integrable hT hj n))
    ((upperAverage_measurable hT.measurable hf).sub (upperAverage_measurable hT.measurable hg))
    ?_ (average_L1_difference_bound hT hf hg hi hj)).2
  filter_upwards [birkhoff_ae_tendsto hT hf hi,birkhoff_ae_tendsto hT hg hj] with ω h1 h2
  exact h1.sub h2

end KingmanSubadditive.Ergodic.Proof
-- End BirkhoffLimit

-- Begin BirkhoffL1Convergence

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma bounded_average_L1_tendsto (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {B : ℝ} (hB : 0≤B)
    (hb : ∀ ω,|f ω|≤B) :
    Tendsto (fun n=>∫ ω,|ergodicAverage T f n ω-upperAverage T f ω| ∂μ) atTop (𝓝 0) := by
  obtain ⟨ξ,_,_,hξ,hl,_⟩ := bounded_birkhoff_convergence hT hf hi hB hb
  have he : upperAverage T f =ᵐ[μ] ξ := by
    filter_upwards [birkhoff_ae_tendsto hT hf hi,hξ] with ω h1 h2
    exact tendsto_nhds_unique h1 h2
  apply hl.congr
  intro n
  exact integral_congr_ae (he.mono fun ω hω=>by dsimp only; rw [hω])

lemma birkhoff_L1_tendsto (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    Tendsto (fun n=>∫ ω,|ergodicAverage T f n ω-upperAverage T f ω| ∂μ) atTop (𝓝 0) := by
  have hξ := birkhoff_limit_integrable hT hf hi
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := ((truncation_L1_tendsto hf hi).eventually (gt_mem_nhds (show 0<ε/4 by positivity))).exists
  let g := boundedTruncation f N
  have hg : Measurable g := truncation_measurable hf N
  have hj : Integrable g μ := truncation_integrable hi N
  have hη := birkhoff_limit_integrable hT hg hj
  have hgL := bounded_average_L1_tendsto hT hg hj (Nat.cast_nonneg N) (truncation_abs_bound f N)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hgL.eventually (gt_mem_nhds (show 0<ε/2 by positivity)))
  refine ⟨M,fun n hn=>?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun ω=>abs_nonneg _)]
  have hb : (∫ ω,|ergodicAverage T f n ω-upperAverage T f ω| ∂μ) ≤
      (∫ ω,|ergodicAverage T f n ω-ergodicAverage T g n ω| ∂μ)+
      (∫ ω,|ergodicAverage T g n ω-upperAverage T g ω| ∂μ)+
      ∫ ω,|upperAverage T f ω-upperAverage T g ω| ∂μ := by
    have hA : Integrable (fun ω=>|ergodicAverage T f n ω-ergodicAverage T g n ω|) μ :=
      ((average_integrable hT hi n).sub (average_integrable hT hj n)).abs
    have hB : Integrable (fun ω=>|ergodicAverage T g n ω-upperAverage T g ω|) μ :=
      ((average_integrable hT hj n).sub hη).abs
    have hC : Integrable (fun ω=>|upperAverage T f ω-upperAverage T g ω|) μ := (hξ.sub hη).abs
    have hAB : Integrable (fun ω=>|ergodicAverage T f n ω-ergodicAverage T g n ω|+|ergodicAverage T g n ω-upperAverage T g ω|) μ := hA.add hB
    rw [← integral_add hA hB,← integral_add hAB hC]
    have hm := integral_mono ((average_integrable hT hi n).sub hξ).abs
      ((hA.add hB).add hC) (fun ω => ?_)
    · simpa only [Pi.add_apply,Pi.abs_apply,Pi.sub_apply] using hm
    · dsimp only [Pi.add_apply,Pi.sub_apply]
      have hh1 := abs_sub_le (ergodicAverage T f n ω) (ergodicAverage T g n ω) (upperAverage T f ω)
      have hh2 := abs_sub_le (ergodicAverage T g n ω) (upperAverage T g ω) (upperAverage T f ω)
      rw [abs_sub_comm (upperAverage T g ω) (upperAverage T f ω)] at hh2
      linarith
  have h1 := average_L1_difference_bound hT hf hg hi hj n
  have h2 := birkhoff_limit_L1_difference hT hf hg hi hj
  have h3 := hM n hn
  change (∫ ω,|f ω-g ω| ∂μ)<ε/4 at hN
  linarith

end KingmanSubadditive.Ergodic.Proof
-- End BirkhoffL1Convergence

-- Begin BirkhoffConvergence

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma birkhoff_convergence (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    ∃ ξ : Ω → ℝ, Measurable ξ ∧ Integrable ξ μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n=>ergodicAverage T f n ω) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun n=>∫ ω,|ergodicAverage T f n ω-ξ ω| ∂μ) atTop (𝓝 0) ∧
      (∫ ω,ξ ω ∂μ) = ∫ ω,f ω ∂μ := by
  have hξ := birkhoff_limit_integrable hT hf hi
  have hl := birkhoff_L1_tendsto hT hf hi
  refine ⟨upperAverage T f,upperAverage_measurable hT.measurable hf,hξ,
    birkhoff_ae_tendsto hT hf hi,hl,?_⟩
  have hb : |(∫ ω,f ω ∂μ)-(∫ ω,upperAverage T f ω ∂μ)|≤0 := by
    apply ge_of_tendsto hl
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← integral_average hT hf hi (Nat.ne_of_gt hn),← integral_sub (average_integrable hT hi n) hξ]
    exact abs_integral_le_integral_abs
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))).symm

end KingmanSubadditive.Ergodic.Proof
-- End BirkhoffConvergence

-- Begin ExpectationSqueeze

open MeasureTheory Filter
open scoped Topology ENNReal

namespace SolomonRWRE.DiffEq.Proof

lemma ae_tendsto_of_expected_domination {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : ℝ≥0∞} (hA : A ≠ ⊤)
    {a : ℕ → Ω → ℝ≥0∞} {b : ℕ → Ω → ℝ} {ξ : Ω → ℝ}
    (hξ : Integrable ξ μ) (hξnn : ∀ᵐ ω ∂μ, 0 ≤ ξ ω)
    (hmean : (∫ ω, ξ ω ∂μ) = A.toReal)
    (hlower : ∀ᵐ ω ∂μ, A ≤ liminf (fun n => a n ω) atTop)
    (hdom : ∀ᵐ ω ∂μ, ∀ n, a n ω ≤ ENNReal.ofReal (b n ω))
    (hb : ∀ᵐ ω ∂μ, Tendsto (fun n => b n ω) atTop (𝓝 (ξ ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => a n ω) atTop (𝓝 A) := by
  have hle : (fun _ : Ω => A.toReal) ≤ᵐ[μ] ξ := by
    filter_upwards [hlower, hdom, hb, hξnn] with ω hlo hd ht hn
    have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    have h : A ≤ ENNReal.ofReal (ξ ω) :=
      hlo.trans ((liminf_le_liminf (Eventually.of_forall hd)).trans_eq ht'.liminf_eq)
    have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
    simpa [ENNReal.toReal_ofReal hn] using hh
  have heq : (fun _ : Ω => A.toReal) =ᵐ[μ] ξ := by
    apply (integral_eq_iff_of_ae_le (integrable_const _) hξ hle).mp
    simpa using hmean.symm
  filter_upwards [hlower, hdom, hb, heq] with ω hlo hd ht he
  apply tendsto_of_le_liminf_of_limsup_le hlo
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  have hsup := (limsup_le_limsup (Eventually.of_forall hd)).trans_eq ht'.limsup_eq
  simpa [← he, ENNReal.ofReal_toReal hA] using hsup

end SolomonRWRE.DiffEq.Proof
-- End ExpectationSqueeze

-- Begin CanonicalLimit

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal
open KingmanSubadditive.Ergodic.Proof

namespace SolomonRWRE.DiffEq.Proof

lemma canonical_limit_of_lower (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hν : marginalMean ρ < 1)
    (hlower : ∀ᵐ x ∂pathMeasure ρ, marginalMean ρ / (1 - marginalMean ρ) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z pathSigma m x) / n)) atTop) :
    ∀ᵐ x ∂pathMeasure ρ,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z pathSigma m x) / n)) atTop
        (𝓝 (marginalMean ρ / (1 - marginalMean ρ))) := by
  rcases birkhoff_convergence (pathShift_preserving ρ)
    forwardPerpetuity_measurable.ennreal_toReal (forwardPerpetuity_integrable ρ hν) with
    ⟨ξ, _, hξ, ht, _, hmean⟩
  have hξnn : ∀ᵐ x ∂pathMeasure ρ, 0 ≤ ξ x := by
    filter_upwards [ht] with x hx
    apply ge_of_tendsto hx
    exact Eventually.of_forall fun n => by
      unfold ergodicAverage birkhoffSum
      positivity
  apply ae_tendsto_of_expected_domination (mean_ratio_ne_top hν) hξ hξnn
    (hmean.trans (forwardPerpetuity_integral ρ hν)) hlower _ ht
  filter_upwards [forwardPerpetuity_all_shifts_finite ρ hν] with x hx n
  exact ENNReal.ofReal_le_ofReal (average_le_perpetuity_average x n hx)

end SolomonRWRE.DiffEq.Proof
-- End CanonicalLimit

-- Begin NativeLimitTransfer

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace SolomonRWRE.DiffEq.Proof

lemma native_limit_of_canonical {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {σ : ℕ → Ω → ℝ} (hσ : IsIIDNonneg P σ)
    (h : ∀ᵐ x ∂pathMeasure (trajectoryMarginal P σ),
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z pathSigma m x) / n)) atTop
        (𝓝 (marginalMean (trajectoryMarginal P σ) /
          (1 - marginalMean (trajectoryMarginal P σ))))) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z σ m ω) / n)) atTop
        (𝓝 (nu P σ / (1 - nu P σ))) := by
  have hmap : MeasurePreserving (trajectory σ) P (pathMeasure (trajectoryMarginal P σ)) :=
    ⟨trajectory_measurable hσ, trajectory_map hσ⟩
  have ht := hmap.quasiMeasurePreserving.ae h
  filter_upwards [ht] with ω hω
  simpa only [trajectory_Z hσ, trajectory_mean hσ] using hω

lemma finite_mean_limit_of_canonical_lower {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {σ : ℕ → Ω → ℝ}
    (hσ : IsIIDNonneg P σ) (hν : nu P σ < 1)
    (hlower : ∀ᵐ x ∂pathMeasure (trajectoryMarginal P σ),
      (∑' k : ℕ, marginalMean (trajectoryMarginal P σ) ^ (k + 1)) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z pathSigma m x) / n)) atTop) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Icc 1 n, Z σ m ω) / n)) atTop
        (𝓝 (nu P σ / (1 - nu P σ))) := by
  let := trajectoryMarginal_probability hσ
  apply native_limit_of_canonical hσ
  apply canonical_limit_of_lower _ (by simpa only [trajectory_mean hσ] using hν)
  simpa only [ENNReal.tsum_geometric_add_one, div_eq_mul_inv] using hlower

end SolomonRWRE.DiffEq.Proof
-- End NativeLimitTransfer

-- Begin InfiniteBoundary

open Filter
open scoped Topology ENNReal

namespace SolomonRWRE.DiffEq.Proof

lemma tsum_pow_succ_of_one_le {ν : ℝ≥0∞} (h : 1 ≤ ν) :
    (∑' k : ℕ, ν ^ (k + 1)) = ⊤ := by
  rw [ENNReal.tsum_geometric_add_one, tsub_eq_zero_of_le h, ENNReal.inv_zero]
  exact ENNReal.mul_top (ne_of_gt (lt_of_lt_of_le zero_lt_one h))

lemma tendsto_top_of_liminf_top {f : ℕ → ℝ≥0∞} (h : liminf f atTop = ⊤) :
    Tendsto f atTop (𝓝 ⊤) :=
  tendsto_of_le_liminf_of_limsup_le (ge_of_eq h) le_top

lemma tendsto_top_of_tsum_le_liminf {ν : ℝ≥0∞} (hν : 1 ≤ ν)
    {f : ℕ → ℝ≥0∞} (h : (∑' k : ℕ, ν ^ (k + 1)) ≤ liminf f atTop) :
    Tendsto f atTop (𝓝 ⊤) := by
  rw [tsum_pow_succ_of_one_le hν] at h
  exact tendsto_top_of_liminf_top (top_le_iff.mp h)

end SolomonRWRE.DiffEq.Proof
-- End InfiniteBoundary

-- Begin RootAssembly

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

open Proof

theorem theorem_4_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) :
    (nu P σ < 1 → ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ k ∈ Finset.Icc 1 n, Z σ k ω) / n)) atTop
        (𝓝 (nu P σ / (1 - nu P σ)))) ∧
    (1 ≤ nu P σ → ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ k ∈ Finset.Icc 1 n, Z σ k ω) / n)) atTop
        (𝓝 ⊤)) := by
  constructor
  · intro hν
    let := trajectoryMarginal_probability hσ
    apply finite_mean_limit_of_canonical_lower hσ hν
    have hl := native_liminf_lower (pathMeasure (trajectoryMarginal P σ)) pathSigma
      (pathSigma_iid (trajectoryMarginal P σ))
    simpa only [pathSigma_mean] using hl
  · intro hν
    filter_upwards [native_liminf_lower P σ hσ] with ω hω
    exact tendsto_top_of_tsum_le_liminf hν hω

end SolomonRWRE.DiffEq
-- End RootAssembly

-- Begin Solution

open MeasureTheory ProbabilityTheory Filter Topology SolomonRWRE.DiffEq

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) :
    (nu P σ < 1 → ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ k ∈ Finset.Icc 1 n, Z σ k ω) / n)) atTop
        (𝓝 (nu P σ / (1 - nu P σ)))) ∧
    (1 ≤ nu P σ → ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ k ∈ Finset.Icc 1 n, Z σ k ω) / n)) atTop
        (𝓝 ⊤)) := theorem_4_4 P σ hσ
-- End Solution

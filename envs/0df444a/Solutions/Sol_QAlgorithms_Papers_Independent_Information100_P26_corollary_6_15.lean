-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.corollary_6_15
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:23:32.842281+00:00
-- url     : https://prove2.me/submissions/010c6301-2d1a-4547-9273-5721445d9a9c

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_4_7

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8C6

variable {d : ℕ}

lemma dep_apply (p q : Fin d × Fin d) :
    depolarizing d p q = if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0 := rfl

lemma ad_apply (B : Mat d) (p q : Fin d × Fin d) : ad B p q = B p.1 q.1 * conj (B p.2 q.2) := rfl

lemma applyMap_apply (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ q : Fin d × Fin d, t (i, j) q * X q.1 q.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

lemma am_mul (s r : Map d) (X : Mat d) :
    applyMap (s * r) X = applyMap s (applyMap r X) := by
  ext i j
  simp only [applyMap_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  ring

lemma am_ad (B : Mat d) (X : Mat d) : applyMap (ad B) X = B * X * Bᴴ := by
  ext i j
  rw [applyMap_apply]
  simp only [ad, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma am_sum {K : Type*} [Fintype K] (M : K → Map d) (X : Mat d) :
    applyMap (∑ k, M k) X = ∑ k, applyMap (M k) X := by
  ext i j
  simp only [applyMap_apply, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ent_single' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (r s i j : n) :
    (A * Matrix.single r s (1 : ℂ) * Aᴴ) i j = A i r * conj (A j s) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Finset.sum_eq_single r]
    · simp [Complex.star_def]
    · intro b _ hb; simp only [Matrix.single_apply]; rw [if_neg (fun h => hb h.1.symm)]; simp
    · simp
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _; simp [Matrix.single_apply, Ne.symm hb]
  · simp

lemma kraus_form {t : Map d} (ht : UnitalChannel t) :
    ∃ m : ℕ, ∃ E : Fin m → Mat d, (∑ j, (E j)ᴴ * E j = 1) ∧ t = ∑ j, ad (E j) := by
  obtain ⟨m, E, hK, hE⟩ := ht.1
  refine ⟨m, E, hK, ?_⟩
  ext p q
  have h := congrFun (congrFun (hE (Matrix.single q.1 q.2 1)) p.1) p.2
  rw [applyMap_apply, Finset.sum_eq_single q] at h
  · rw [Matrix.sum_apply]
    simp only [Matrix.single_apply, and_self, if_true, mul_one] at h
    rw [h]
    simp only [QAlgorithms.krausApply, Matrix.sum_apply, ent_single']
    rfl
  · intro b _ hb
    rw [Matrix.single_apply, if_neg (fun c => hb (Prod.ext c.1.symm c.2.symm)), mul_zero]
  · simp

lemma isChannel_of_kraus {K ι : Type*} [Fintype K] [Fintype ι] [DecidableEq ι]
    (E : K → Matrix ι ι ℂ) (hE : QAlgorithms.IsKrausFamily E) (Φ : QAlgorithms.Superop ι ι)
    (hΦ : ∀ ρ, Φ ρ = QAlgorithms.krausApply E ρ) : QAlgorithms.IsChannel Φ := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (e.symm j), ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily at hE ⊢
    rw [← hE]
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · intro ρ
    rw [hΦ]
    unfold QAlgorithms.krausApply
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

lemma ad_mul (A B : Mat d) : ad A * ad B = ad (A * B) := by
  ext p q
  simp only [Matrix.mul_apply, ad_apply, Fintype.sum_prod_type, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma uc_mul {s r : Map d} (hs : UnitalChannel s) (hr : UnitalChannel r) :
    UnitalChannel (s * r) := by
  obtain ⟨m, E, hE, rfl⟩ := kraus_form hs
  obtain ⟨m', F, hF, rfl⟩ := kraus_form hr
  have hunit : applyMap ((∑ j, ad (E j)) * ∑ j, ad (F j)) 1 = 1 := by
    rw [am_mul, hr.2, hs.2]
  refine ⟨?_, hunit⟩
  let G : Fin m × Fin m' → Mat d := fun k => E k.1 * F k.2
  refine isChannel_of_kraus G ?_ _ ?_
  · unfold QAlgorithms.IsKrausFamily
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [G, Matrix.conjTranspose_mul]
    have : ∀ y : Fin m', ∑ x : Fin m, (F y)ᴴ * (E x)ᴴ * (E x * F y) = (F y)ᴴ * F y := by
      intro y
      calc ∑ x : Fin m, (F y)ᴴ * (E x)ᴴ * (E x * F y)
          = (F y)ᴴ * (∑ x, (E x)ᴴ * E x) * F y := by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun x _ => by noncomm_ring
        _ = (F y)ᴴ * F y := by rw [hE, Matrix.mul_one]
    simp only [this]
    exact hF
  · intro ρ
    rw [am_mul, am_sum, am_sum]
    simp only [am_ad, QAlgorithms.krausApply, G, Fintype.sum_prod_type, Finset.mul_sum,
      Finset.sum_mul, Matrix.conjTranspose_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    noncomm_ring

lemma uc_pow {t : Map d} (ht : UnitalChannel t) (n : ℕ) (hn : 1 ≤ n) :
    UnitalChannel (t ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => rwa [pow_one]
  | succ n _ ih => rw [pow_succ]; exact uc_mul ih ht

lemma col_le {m : ℕ} (E : Fin m → Mat d) (hE : ∑ j, (E j)ᴴ * E j = 1) (a b : Fin d) :
    ∑ j, Complex.normSq (E j a b) ≤ 1 := by
  have h := congrFun (congrFun hE b) b
  rw [Matrix.sum_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def] at h
  have h' : ∑ j, ∑ i, Complex.normSq (E j i b) = 1 := by
    have := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.one_re] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    generalize E j i b = z
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]; ring
  rw [← h']
  refine Finset.sum_le_sum fun j _ => ?_
  exact Finset.single_le_sum (f := fun i => Complex.normSq (E j i b))
    (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

lemma entry_le {t : Map d} (ht : UnitalChannel t) (p q : Fin d × Fin d) : ‖t p q‖ ≤ 1 := by
  obtain ⟨m, E, hE, rfl⟩ := kraus_form ht
  rw [Matrix.sum_apply]
  calc ‖∑ j, ad (E j) p q‖ ≤ ∑ j, ‖ad (E j) p q‖ := norm_sum_le _ _
    _ ≤ ∑ j, (Complex.normSq (E j p.1 q.1) + Complex.normSq (E j p.2 q.2)) / 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [ad_apply, norm_mul, Complex.norm_conj, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg (‖E j p.1 q.1‖ - ‖E j p.2 q.2‖)]
    _ = (∑ j, Complex.normSq (E j p.1 q.1) + ∑ j, Complex.normSq (E j p.2 q.2)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ 1 := by linarith [col_le E hE p.1 q.1, col_le E hE p.2 q.2]

end X8C6

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8C6

variable {d : ℕ}

def TPm (M : Map d) : Prop := ∀ q : Fin d × Fin d, ∑ i, M (i,i) q = if q.1 = q.2 then 1 else 0

def Um (M : Map d) : Prop := ∀ p : Fin d × Fin d, ∑ i, M p (i,i) = if p.1 = p.2 then 1 else 0

lemma sum_diag (f : Fin d × Fin d → ℂ) :
    ∑ r : Fin d × Fin d, (if r.1 = r.2 then (1 : ℂ) else 0) * f r = ∑ j, f (j, j) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x] <;> simp_all [eq_comm]

lemma sum_diag' (f : Fin d × Fin d → ℂ) :
    ∑ r : Fin d × Fin d, f r * (if r.1 = r.2 then (1 : ℂ) else 0) = ∑ j, f (j, j) := by
  rw [← sum_diag]; exact Finset.sum_congr rfl fun r _ => mul_comm _ _

lemma tp_sum {m : ℕ} (E : Fin m → Mat d) (hK : ∑ j, (E j)ᴴ * E j = 1) :
    TPm (∑ j, ad (E j)) := by
  intro q
  have h := congrFun (congrFun hK q.2) q.1
  rw [Matrix.sum_apply] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
  simp only [Matrix.sum_apply, ad_apply]
  rw [Finset.sum_comm]
  have e : (if q.1 = q.2 then (1 : ℂ) else 0) = if q.2 = q.1 then 1 else 0 := by
    simp only [eq_comm]
  rw [e, ← h]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [Complex.star_def]; ring

lemma tp_of {t : Map d} (ht : UnitalChannel t) : TPm t := by
  obtain ⟨m, E, hE, rfl⟩ := kraus_form ht
  exact tp_sum E hE

lemma un_of {t : Map d} (ht : UnitalChannel t) : Um t := by
  intro p
  have h := congrFun (congrFun ht.2 p.1) p.2
  rw [applyMap_apply] at h
  rw [← sum_diag']
  rw [Matrix.one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.one_apply]

lemma dep_mul {M : Map d} (hM : TPm M) : depolarizing d * M = depolarizing d := by
  ext p q
  simp only [Matrix.mul_apply, dep_apply]
  rw [Fintype.sum_prod_type]
  by_cases hp : p.1 = p.2
  · simp only [hp, true_and, ite_mul, zero_mul]
    have : ∀ x : Fin d, (∑ y : Fin d, if x = y then (d : ℂ)⁻¹ * M (x, y) q else 0) =
        (d : ℂ)⁻¹ * M (x, x) q := fun x => by simp
    simp only [this, ← Finset.mul_sum, hM q]
    split_ifs <;> simp
  · simp [hp]

lemma mul_dep {M : Map d} (hM : Um M) : M * depolarizing d = depolarizing d := by
  ext p q
  simp only [Matrix.mul_apply, dep_apply]
  rw [Fintype.sum_prod_type]
  by_cases hq : q.1 = q.2
  · simp only [hq, and_true, mul_ite, mul_zero]
    have : ∀ x : Fin d, (∑ y : Fin d, if x = y then M p (x, y) * (d : ℂ)⁻¹ else 0) =
        M p (x, x) * (d : ℂ)⁻¹ := fun x => by simp
    simp only [this, ← Finset.sum_mul, hM p]
    split_ifs <;> simp
  · simp [hq]

lemma un_dep [NeZero d] : Um (depolarizing d) := by
  intro p
  simp only [dep_apply, and_true]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  split_ifs <;> simp [hd]

lemma ring_pow {R : Type*} [Ring R] (t e : R) (h1 : t * e = e) (h2 : e * t = e)
    (h3 : e * e = e) (n : ℕ) (hn : 1 ≤ n) : (t - e) ^ n = t ^ n - e := by
  have hte : ∀ k : ℕ, t ^ (k + 1) * e = e := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one, h1]
    | succ k ih => rw [pow_succ, mul_assoc, h1, ih]
  induction n, hn using Nat.le_induction with
  | base => rw [pow_one, pow_one]
  | succ n hn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, ih, pow_succ (t) (k + 1)]
    have := hte k
    rw [sub_mul, mul_sub, mul_sub, this, h2, h3]
    abel

lemma mulVec_pow {t : Map d} {v : Fin d × Fin d → ℂ} {z : ℂ} (h : t *ᵥ v = z • v) (n : ℕ) :
    (t ^ n) *ᵥ v = z ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- eigenvalues of `t - δ` have modulus `< 1` -/
lemma eig_lt [NeZero d] {t : Map d} (ht : UnitalChannel t) (hprim : Primitive t)
    {z : ℂ} {v : Fin d × Fin d → ℂ} (hv : v ≠ 0)
    (hz : (t - depolarizing d) *ᵥ v = z • v) : ‖z‖ < 1 := by
  set δ := depolarizing d
  have hδt : δ * t = δ := dep_mul (tp_of ht)
  have htδ : t * δ = δ := mul_dep (un_of ht)
  have hδδ : δ * δ = δ := mul_dep un_dep
  have hδN : δ * (t - δ) = 0 := by rw [mul_sub, hδt, hδδ, sub_self]
  by_cases hz0 : z = 0
  · rw [hz0]; simp
  have hδv : δ *ᵥ v = 0 := by
    have h1 : δ *ᵥ ((t - δ) *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, hδN, Matrix.zero_mulVec]
    rw [hz, Matrix.mulVec_smul] at h1
    exact (smul_eq_zero.mp h1).resolve_left hz0
  have htv : t *ᵥ v = z • v := by
    have : t = (t - δ) + δ := by abel
    rw [this, Matrix.add_mulVec, hz, hδv, add_zero]
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · exact h
  · exfalso
    let X : Mat d := fun i j => v (i, j)
    have hX : applyMap t X = z • X := by
      ext i j
      rw [applyMap_apply]
      have := congrFun htv (i, j)
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply] at this
      rw [Matrix.smul_apply, ← this]
    have hmem : X ∈ peripheral t := Submodule.subset_span ⟨z, h, hX⟩
    rw [hprim, scalars, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have htr : ∑ k, v (k, k) = 0 := by
      have := congrFun hδv (p.1, p.1)
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      have e1 : ∀ q : Fin d × Fin d, δ (p.1, p.1) q * v q =
          (d : ℂ)⁻¹ * ((if q.1 = q.2 then 1 else 0) * v q) := by
        intro q; simp only [δ, dep_apply, true_and]; split_ifs <;> ring
      rw [Finset.sum_congr rfl fun q _ => e1 q, ← Finset.mul_sum, sum_diag] at this
      have hd : (d : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne d))
      exact (mul_eq_zero.mp this).resolve_left hd
    have hc0 : c = 0 := by
      have : ∑ k : Fin d, X k k = c * d := by
        rw [← hc]
        simp only [X, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [show (∑ k : Fin d, X k k) = ∑ k, v (k, k) from rfl, htr] at this
      have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
      exact ((mul_eq_zero.mp this.symm).resolve_right hd)
    apply hp
    have := congrFun (congrFun hc p.1) p.2
    rw [hc0, zero_smul] at this
    exact this.symm
  · exfalso
    set S := ∑ q, ‖v q‖
    have hvp : 0 < ‖v p‖ := norm_pos_iff.mpr hp
    have hT := tendsto_pow_atTop_atTop_of_one_lt h
    obtain ⟨n, hn, hn1⟩ := ((hT.eventually_gt_atTop (S / ‖v p‖)).and
      (eventually_ge_atTop 1)).exists
    have hb : ‖z‖ ^ n * ‖v p‖ ≤ S := by
      have e := congrFun (mulVec_pow htv n) p
      rw [Pi.smul_apply, smul_eq_mul] at e
      calc ‖z‖ ^ n * ‖v p‖ = ‖((t ^ n) *ᵥ v) p‖ := by rw [e, norm_mul, norm_pow]
        _ ≤ ∑ q, ‖(t ^ n) p q * v q‖ := norm_sum_le _ _
        _ ≤ ∑ q, ‖v q‖ := Finset.sum_le_sum fun q _ => by
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (entry_le (uc_pow ht n hn1) p q)
    rw [div_lt_iff₀ hvp] at hn
    linarith

lemma hsNorm_eq (M : Map d) : hsNorm M = ‖M‖ := by
  rw [Matrix.frobenius_norm_def, hsNorm, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

lemma spec_lt [NeZero d] {t : Map d} (ht : UnitalChannel t) (hprim : Primitive t)
    {z : ℂ} (hz : z ∈ spectrum ℂ (t - depolarizing d)) : ‖z‖ < 1 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hz
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  refine eig_lt ht hprim hv ?_
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_eq_zero] at hv0
  exact hv0.symm

lemma conv [NeZero d] {t : Map d} (ht : UnitalChannel t) (hprim : Primitive t) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ᶠ n : ℕ in atTop, ‖(t - depolarizing d) ^ n‖ < c ^ n := by
  set N := t - depolarizing d
  obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius N
  have hz1 : ‖z‖ < 1 := spec_lt ht hprim hz
  set c : ℝ := (‖z‖ + 1) / 2
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by simp only [c]; linarith
  refine ⟨c, hc0, hc1, ?_⟩
  have hlim := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius N
  have hlt : spectralRadius ℂ N < ENNReal.ofReal c := by
    have e : ((‖z‖₊ : NNReal) : ENNReal) = ENNReal.ofReal ‖z‖ := by
      rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
    rw [← hzr, e, ENNReal.ofReal_lt_ofReal_iff (by simp only [c]; positivity)]
    simp only [c]; linarith
  filter_upwards [hlim.eventually_lt_const hlt, eventually_ge_atTop 1] with n hn hn1
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at hn
  have hx : 0 ≤ ‖N ^ n‖ := norm_nonneg _
  have := pow_lt_pow_left₀ hn (by positivity) (by omega : n ≠ 0)
  rwa [one_div, Real.rpow_inv_natCast_pow hx (by omega)] at this

theorem x8_main {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (hprim : Primitive t) : Eventually MTD t := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨e, he, hMTD⟩ := theorem_4_7 hd
  obtain ⟨c, hc0, hc1, hev⟩ := conv ht hprim
  have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  have hev2 := hpow.eventually (gt_mem_nhds he)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hev.and (hev2.and (eventually_ge_atTop 1)))
  refine ⟨max N0 1, le_max_right _ _, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN0 n (le_of_max_le_left hn)
  apply hMTD _ (uc_pow ht n h3)
  rw [hsNorm_eq, ← ring_pow t (depolarizing d) (mul_dep (un_of ht)) (dep_mul (tp_of ht))
    (mul_dep un_dep) n h3]
  linarith

end X8C6

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (hprim : Primitive t) : Eventually MTD t :=
  QAlgorithms.Papers.Independent.Information100.P26.X8C6.x8_main hd t ht hprim

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.corollary_4_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:44:20.780841+00:00
-- url     : https://prove2.me/submissions/59029dfa-7fd2-454a-8625-2fc00f1b5e53

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

open Module
open scoped Matrix ComplexOrder ComplexConjugate BigOperators

noncomputable section

namespace X6P26C

open QAlgorithms.Papers.Independent.Information100.P26

/-- X ↦ tr(P_v X) P_u as a matrix-unit tensor. -/
def E4 {d : ℕ} (u v : Fin d → ℂ) : Map d :=
  fun p q => u p.1 * conj (u p.2) * (conj (v q.1) * v q.2)

theorem adD {d : ℕ} (U : Mat d) (p r : Fin d × Fin d) :
    (ad U * dephasing d) p r = if r.1 = r.2 then ad U p r else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · simp only [dephasing, and_true]; split_ifs <;> simp
  · intro b _ hb; simp only [dephasing]; split_ifs with h
    · exact absurd h.2 hb
    · simp
  · simp

theorem sum_diag {d : ℕ} (f : Fin d × Fin d → ℂ) :
    ∑ r : Fin d × Fin d, (if r.1 = r.2 then f r else 0) = ∑ k, f (k, k) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k] <;> simp +contextual [eq_comm]

theorem beta_apply {d : ℕ} (U V : Unitary d) (p q : Fin d × Fin d) :
    beta U V p q = ∑ k, (U : Mat d) p.1 k * conj ((U : Mat d) p.2 k) *
      (conj ((V : Mat d) q.1 k) * (V : Mat d) q.2 k) := by
  unfold beta
  rw [Matrix.mul_apply]
  simp only [adD, ite_mul, zero_mul]
  rw [sum_diag]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ad, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem beta_eq {d : ℕ} (U V : Unitary d) :
    beta U V = ∑ k, E4 (fun i => (U : Mat d) i k) (fun i => (V : Mat d) i k) := by
  ext p q
  rw [beta_apply, Matrix.sum_apply]
  rfl

def col {d : ℕ} (U : Unitary d) (k : Fin d) : Fin d → ℂ := fun a => (U : Mat d) a k

/-- zero-sum real combinations of twisted maps -/
def L (d : ℕ) : Submodule ℝ (Map d) :=
  (LinearMap.ker (Finsupp.linearCombination ℝ (fun _ : Unitary d × Unitary d => (1:ℝ)))).map
    (Finsupp.linearCombination ℝ (fun x : Unitary d × Unitary d => beta x.1 x.2))

theorem diff_mem {d : ℕ} (U1 V1 U2 V2 : Unitary d) : beta U1 V1 - beta U2 V2 ∈ L d := by
  refine ⟨Finsupp.single (U1, V1) 1 - Finsupp.single (U2, V2) 1, ?_, ?_⟩
  · simp [LinearMap.mem_ker]
  · simp

def colPerm {d : ℕ} (U : Unitary d) (σ : Equiv.Perm (Fin d)) : Unitary d :=
  ⟨(U : Mat d).submatrix id σ, by
    have h := Matrix.mem_unitaryGroup_iff.1 U.2
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.mul_apply] at this ⊢
    simp only [Matrix.submatrix_apply, id, Matrix.star_apply] at this ⊢
    rw [← this]
    exact Equiv.sum_comp σ (fun k => (U : Mat d) i k * star ((U : Mat d) j k))⟩

theorem beta_colPerm {d : ℕ} (U V : Unitary d) (σ : Equiv.Perm (Fin d)) :
    beta (colPerm U σ) V = ∑ k, E4 (col U (σ k)) (col V k) := by
  rw [beta_eq]; rfl

theorem swap_diff {d : ℕ} (f : Fin d → Fin d → Map d) (σ : Equiv.Perm (Fin d)) (o i : Fin d)
    (hoi : o ≠ i) :
    ∑ k, f k (σ k) - ∑ k, f k ((σ * Equiv.swap o i) k) =
      f o (σ o) + f i (σ i) - f o (σ i) - f i (σ o) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ {o, i})]
  · rw [Finset.sum_pair hoi]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    abel
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]

theorem box_mem {d : ℕ} (U V : Unitary d) (o i j : Fin d) :
    E4 (col U j) (col V i) - E4 (col U j) (col V o) - E4 (col U o) (col V i)
      + E4 (col U o) (col V o) ∈ L d := by
  by_cases hi : i = o
  · subst hi; simp
  by_cases hj : j = o
  · subst hj; simp
  have h := diff_mem (colPerm U (Equiv.swap i j)) V (colPerm U (Equiv.swap i j * Equiv.swap o i)) V
  rw [beta_colPerm, beta_colPerm,
    swap_diff (fun k m => E4 (col U m) (col V k)) _ o i (Ne.symm hi)] at h
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)] at h
  convert h using 1
  abel

theorem herm_expand {d : ℕ} {H : Mat d} (hH : H.IsHermitian) (a b : Fin d) :
    H a b = ∑ i, (hH.eigenvectorUnitary : Mat d) a i * (hH.eigenvalues i : ℂ) *
      conj ((hH.eigenvectorUnitary : Mat d) b i) := by
  conv_lhs => rw [hH.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.star_apply, Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, RCLike.star_def]
  rfl

/-- X ↦ tr(H X) K -/
def R {d : ℕ} (H K : Mat d) : Map d := fun p q => K p.1 p.2 * H q.2 q.1

theorem R_spec {d : ℕ} {H K : Mat d} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    R H K = ∑ i, ∑ j, (hH.eigenvalues i * hK.eigenvalues j) •
      E4 (col hK.eigenvectorUnitary j) (col hH.eigenvectorUnitary i) := by
  ext p q
  simp only [R, Matrix.sum_apply, Matrix.smul_apply, E4, col]
  rw [herm_expand hK, herm_expand hH, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.real_smul]; push_cast; ring

theorem R_mem {d : ℕ} (hd : 0 < d) {H K : Mat d} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (htH : H.trace = 0) (htK : K.trace = 0) : R H K ∈ L d := by
  set o : Fin d := ⟨0, hd⟩
  set h := hH.eigenvalues
  set κ := hK.eigenvalues
  set u := col hK.eigenvectorUnitary
  set v := col hH.eigenvectorUnitary
  have sh : ∑ i, h i = 0 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [htH] at this
    exact Complex.ofReal_eq_zero.1 (by rw [Complex.ofReal_sum]; exact this.symm)
  have sk : ∑ i, κ i = 0 := by
    have := hK.trace_eq_sum_eigenvalues
    rw [htK] at this
    exact Complex.ofReal_eq_zero.1 (by rw [Complex.ofReal_sum]; exact this.symm)
  have key : R H K = ∑ i, ∑ j, (h i * κ j) •
      (E4 (u j) (v i) - E4 (u j) (v o) - E4 (u o) (v i) + E4 (u o) (v o)) := by
    rw [R_spec hH hK]
    simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have z1 : ∑ i, ∑ j, (h i * κ j) • E4 (u j) (v o) = 0 := by
      simp_rw [mul_smul, ← Finset.smul_sum, ← Finset.sum_smul, sh, zero_smul]
    have z2 : ∑ i, ∑ j, (h i * κ j) • E4 (u o) (v i) = 0 := by
      simp_rw [mul_comm (h _), mul_smul, ← Finset.sum_smul, sk, zero_smul, Finset.sum_const_zero]
    have z3 : ∑ i, ∑ j, (h i * κ j) • E4 (u o) (v o) = 0 := by
      simp_rw [mul_comm (h _), mul_smul, ← Finset.sum_smul, sk, zero_smul, Finset.sum_const_zero]
    rw [z1, z2, z3]; simp only [sub_zero, add_zero]; rfl
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (box_mem _ _ o i j)

def Φ {d : ℕ} (T : Map d) (k l : Fin d) : Mat d := fun i j => T (i, j) (k, l)

def Eu {d : ℕ} (a b : Fin d) : Mat d := Matrix.single a b 1

theorem decomp {d : ℕ} (T : Map d) : T = ∑ k, ∑ l, R (Eu l k) (Φ T k l) := by
  ext p q
  simp only [Matrix.sum_apply, R, Φ, Eu, Matrix.single_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single q.1]
  · rw [Finset.sum_eq_single q.2]
    · simp
    · intro b _ hb; simp only [ite_eq_right_iff]; intro h; exact absurd h.1 hb
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun l _ => ?_
    simp only [ite_eq_right_iff]; intro h; exact absurd h.2 hb
  · simp

theorem trace_Eu {d : ℕ} (a b : Fin d) : (Eu a b).trace = if a = b then 1 else 0 := by
  unfold Eu
  split_ifs with h
  · subst h; exact Matrix.trace_single_eq_same _ _
  · exact Matrix.trace_single_eq_of_ne _ _ _ h

theorem herm_Eu {d : ℕ} (a b : Fin d) : (Eu a b)ᴴ = Eu b a := by
  unfold Eu; rw [Matrix.conjTranspose_single]; simp

theorem main_L {d : ℕ} (hd : 0 < d) (T : Map d)
    (hHP : ∀ i j k l, conj (T (i, j) (k, l)) = T (j, i) (l, k))
    (hTP : ∀ k l, ∑ i, T (i, i) (k, l) = 0)
    (hU : ∀ i j, ∑ k, T (i, j) (k, k) = 0) : T ∈ L d := by
  set o : Fin d := ⟨0, hd⟩
  let S : Fin d → Fin d → Mat d := fun k l =>
    Eu l k + Eu k l - (if k = l then (2:ℂ) • Eu o o else 0)
  let W : Fin d → Fin d → Mat d := fun k l => Complex.I • (Eu l k - Eu k l)
  let A : Fin d → Fin d → Mat d := fun k l => (1/2 : ℂ) • (Φ T k l + Φ T l k)
  let B : Fin d → Fin d → Mat d := fun k l => (-Complex.I/2) • (Φ T k l - Φ T l k)
  have hΦ : ∀ k l, (Φ T k l)ᴴ = Φ T l k := by
    intro k l; ext i j
    simp only [Matrix.conjTranspose_apply, Φ, RCLike.star_def, hHP]
  have tΦ : ∀ k l, (Φ T k l).trace = 0 := fun k l => hTP k l
  have h3 : ∀ k l, R (Eu l k) (Φ T k l) + R (Eu k l) (Φ T l k) =
      R (S k l) (A k l) + R (W k l) (B k l) +
        (if k = l then R ((2:ℂ) • Eu o o) (A k l) else 0) := by
    intro k l
    ext p q
    split_ifs with hkl
    · simp only [S, W, A, B, R, hkl, if_true, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul]
      ring_nf; try (rw [Complex.I_sq]; ring)
    · simp only [S, W, A, B, R, hkl, if_false, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, sub_zero, add_zero]
      ring_nf; try (rw [Complex.I_sq]; ring)
  have h4 : ∑ k, ∑ l, (if k = l then R ((2:ℂ) • Eu o o) (A k l) else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ext p q
    simp only [Matrix.sum_apply, R, A, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Matrix.zero_apply, Φ]
    rw [← Finset.sum_mul]
    have := hU p.1 p.2
    have e : ∑ k, (1/2 : ℂ) * (T (p.1, p.2) (k, k) + T (p.1, p.2) (k, k)) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, this]; simp
    rw [e, zero_mul]
  have h2T : (2:ℝ) • T = ∑ k, ∑ l, (R (S k l) (A k l) + R (W k l) (B k l)) := by
    have e1 := decomp T
    have e2 : T = ∑ k, ∑ l, R (Eu k l) (Φ T l k) := by
      rw [Finset.sum_comm]; exact e1
    have e3 : (2:ℝ) • T = (∑ k, ∑ l, R (Eu l k) (Φ T k l)) + ∑ k, ∑ l, R (Eu k l) (Φ T l k) := by
      rw [two_smul, ← e1, ← e2]
    rw [e3, ← Finset.sum_add_distrib]
    have : ∀ k, (∑ l, R (Eu l k) (Φ T k l)) + ∑ l, R (Eu k l) (Φ T l k) =
        ∑ l, (R (S k l) (A k l) + R (W k l) (B k l)) +
          ∑ l, (if k = l then R ((2:ℂ) • Eu o o) (A k l) else 0) := by
      intro k; rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => h3 k l
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, h4, add_zero]
  have hT : T = (1/2 : ℝ) • ∑ k, ∑ l, (R (S k l) (A k l) + R (W k l) (B k l)) := by
    rw [← h2T, smul_smul]; norm_num
  rw [hT]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
    Submodule.add_mem _ (R_mem hd ?_ ?_ ?_ ?_) (R_mem hd ?_ ?_ ?_ ?_))
  · -- S hermitian
    simp only [S, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      herm_Eu]
    split_ifs
    · rw [Matrix.conjTranspose_smul, herm_Eu]; simp [add_comm]
    · simp [add_comm]
  · simp only [A, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hΦ]
    simp [add_comm]
  · simp only [S, Matrix.trace_sub, Matrix.trace_add, trace_Eu]
    by_cases h : k = l
    · subst h; simp [trace_Eu, Matrix.trace_smul]; norm_num
    · simp [h, Ne.symm h, trace_Eu]
  · simp only [A, Matrix.trace_smul, Matrix.trace_add, tΦ]; simp
  · simp only [W, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      herm_Eu]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, RCLike.star_def,
      Complex.conj_I]
    ring
  · simp only [B, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hΦ]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, RCLike.star_def, map_div₀,
      map_neg, Complex.conj_I, map_ofNat]
    ring
  · simp only [W, Matrix.trace_smul, Matrix.trace_sub, trace_Eu]
    by_cases h : k = l
    · subst h; simp
    · simp [h, Ne.symm h]
  · simp only [B, Matrix.trace_smul, Matrix.trace_sub, tΦ]; simp

theorem applyMap_apply {d : ℕ} (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ r, t (i, j) r * X r.1 r.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

theorem applyMap_single {d : ℕ} (t : Map d) (i j k l : Fin d) :
    applyMap t (Matrix.single k l 1) i j = t (i, j) (k, l) := by
  rw [applyMap_apply, Finset.sum_eq_single (k, l)]
  · simp
  · intro b _ hb
    simp only [Matrix.single_apply]
    rw [if_neg]; · simp
    rintro ⟨h1, h2⟩; exact hb (Prod.ext h1.symm h2.symm)
  · simp

theorem kraus_entry {d : ℕ} (t : Map d) (ht : QAlgorithms.IsChannel (applyMap t)) :
    ∃ m, ∃ E : Fin m → Mat d, (∑ a, (E a)ᴴ * E a = 1) ∧
      ∀ i j k l, t (i, j) (k, l) = ∑ a, E a i k * conj (E a j l) := by
  obtain ⟨m, E, hE, hΦ⟩ := ht
  refine ⟨m, E, hE, fun i j k l => ?_⟩
  have := congrFun (congrFun (hΦ (Matrix.single k l 1)) i) j
  rw [applyMap_single] at this
  rw [this]
  simp [QAlgorithms.krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem depol_apply {d : ℕ} (i j k l : Fin d) :
    depolarizing d (i, j) (k, l) = if i = j ∧ k = l then (d : ℂ)⁻¹ else 0 := rfl

theorem props {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    (∀ i j k l, conj ((t - depolarizing d) (i, j) (k, l)) = (t - depolarizing d) (j, i) (l, k)) ∧
    (∀ k l, ∑ i, (t - depolarizing d) (i, i) (k, l) = 0) ∧
    (∀ i j, ∑ k, (t - depolarizing d) (i, j) (k, k) = 0) := by
  obtain ⟨m, E, hE, hent⟩ := kraus_entry t ht.1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨fun i j k l => ?_, fun k l => ?_, fun i j => ?_⟩
  · simp only [Matrix.sub_apply, map_sub, depol_apply, hent, map_sum, map_mul,
      Complex.conj_conj]
    congr 1
    · exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    · by_cases h1 : i = j <;> by_cases h2 : k = l <;>
        simp [h1, h2, eq_comm, map_inv₀, Complex.conj_natCast]
  · have h1 := congrFun (congrFun hE l) k
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def] at h1
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib, depol_apply, hent]
    rw [Finset.sum_comm]
    have h2 : ∑ y, ∑ x, E y x k * conj (E y x l) = (1 : Mat d) l k := by
      rw [← h1]; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [h2, Matrix.one_apply]
    by_cases h : k = l
    · subst h; simp [Finset.sum_const, Finset.card_univ]; field_simp; try simp
    · simp [h, Ne.symm h]
  · have h1 := congrFun (congrFun ht.2 i) j
    rw [applyMap_apply] at h1
    have h2 : ∑ r : Fin d × Fin d, t (i, j) r * (1 : Mat d) r.1 r.2 = ∑ k, t (i, j) (k, k) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Matrix.one_apply, Ne.symm hb]
      · simp
    rw [h2] at h1
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib, depol_apply, h1, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp [Finset.sum_const, Finset.card_univ]; field_simp; try simp
    · simp [h]

theorem sum_E4 {d : ℕ} :
    ∑ k : Fin d, ∑ j : Fin d, E4 (col (1 : Unitary d) j) (col (1 : Unitary d) k) =
      (d : ℂ) • depolarizing d := by
  ext p q
  simp only [Matrix.sum_apply, E4, col, Matrix.smul_apply, smul_eq_mul]
  have h1 : ((1 : Unitary d) : Mat d) = 1 := rfl
  simp only [h1, Matrix.one_apply, depolarizing]
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2
  · rw [if_pos ⟨hp, hq⟩]
    simp [hp, hq, Finset.sum_ite_eq', ite_mul]
    have : (d : ℂ) ≠ 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact absurd p.1.isLt (by omega)
      · exact_mod_cast h.ne'
    field_simp
  all_goals
    rw [if_neg (by tauto)]
    simp only [mul_zero]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases a : p.1 = j <;> by_cases b : p.2 = j <;> by_cases c : q.1 = k <;>
      by_cases e : q.2 = k <;> simp [a, b, c, e] <;> subst_vars <;> tauto

theorem dep_eq {d : ℕ} (hd : 0 < d) :
    haveI : NeZero d := ⟨hd.ne'⟩
    depolarizing d = ∑ s : Fin d, (1 / d : ℝ) • beta (colPerm 1 (Equiv.addRight s)) 1 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  simp only [beta_colPerm, Equiv.coe_addRight]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have : ∀ k : Fin d, ∑ s : Fin d, E4 (col (1 : Unitary d) (k + s)) (col 1 k) =
      ∑ j : Fin d, E4 (col (1 : Unitary d) j) (col 1 k) :=
    fun k => Equiv.sum_comp (Equiv.addLeft k) (fun j => E4 (col (1 : Unitary d) j) (col 1 k))
  rw [Finset.sum_congr rfl fun k _ => this k, sum_E4]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [← Complex.coe_smul, smul_smul]
  push_cast
  rw [one_div, inv_mul_cancel₀ hd', one_smul]

theorem of_finsupp {d : ℕ} (h : (Unitary d × Unitary d) →₀ ℝ) :
    ∃ n : ℕ, ∃ a : Fin n → ℝ, ∃ U V : Fin n → Unitary d,
      (∑ j, a j) = Finsupp.linearCombination ℝ (fun _ => (1:ℝ)) h ∧
      (∑ j, a j • beta (U j) (V j)) =
        Finsupp.linearCombination ℝ (fun x : Unitary d × Unitary d => beta x.1 x.2) h := by
  classical
  let e := h.support.equivFin
  refine ⟨h.support.card, fun j => h (e.symm j), fun j => (e.symm j).1.1,
    fun j => (e.symm j).1.2, ?_, ?_⟩
  · rw [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [← Finset.sum_coe_sort h.support]
    simp only [smul_eq_mul, mul_one]
    exact Equiv.sum_comp e.symm (fun x => h x)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [← Finset.sum_coe_sort h.support]
    exact Equiv.sum_comp e.symm (fun x => h x • beta x.1.1 x.1.2)

end X6P26C

open X6P26C

namespace QAlgorithms.Papers.Independent.Information100.P26

theorem cor46 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    ∃ n : ℕ, ∃ a : Fin n → ℝ, ∃ U V : Fin n → Unitary d,
      (∑ j, a j) = 1 ∧ t = ∑ j, a j • beta (U j) (V j) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨p1, p2, p3⟩ := props hd t ht
  obtain ⟨f, hf, hfT⟩ := main_L hd _ p1 p2 p3
  let g : (Unitary d × Unitary d) →₀ ℝ :=
    ∑ s : Fin d, Finsupp.single (colPerm 1 (Equiv.addRight s), (1 : Unitary d)) (1 / d : ℝ)
  have hg1 : Finsupp.linearCombination ℝ (fun _ => (1:ℝ)) g = 1 := by
    simp only [g, map_sum, Finsupp.linearCombination_single, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hg2 : Finsupp.linearCombination ℝ (fun x : Unitary d × Unitary d => beta x.1 x.2) g =
      depolarizing d := by
    simp only [g, map_sum, Finsupp.linearCombination_single]
    exact (dep_eq hd).symm
  obtain ⟨n, a, U, V, h1, h2⟩ := of_finsupp (g + f)
  refine ⟨n, a, U, V, ?_, ?_⟩
  · rw [h1, map_add, hg1, LinearMap.mem_ker.1 hf, add_zero]
  · rw [h2, map_add, hg2, hfT]; abel

end QAlgorithms.Papers.Independent.Information100.P26


open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    ∃ n : ℕ, ∃ a : Fin n → ℝ, ∃ U V : Fin n → Unitary d,
      (∑ j, a j) = 1 ∧ t = ∑ j, a j • beta (U j) (V j) :=
  cor46 hd t ht

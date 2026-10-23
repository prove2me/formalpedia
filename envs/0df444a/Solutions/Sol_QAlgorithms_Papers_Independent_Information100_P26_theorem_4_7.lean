-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.theorem_4_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:54:23.497368+00:00
-- url     : https://prove2.me/submissions/62ad1e9f-04e3-4d55-b175-51fc2daf6c41

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

def box {d : ℕ} (U V : Unitary d) (o i j : Fin d) : Map d :=
  E4 (col U j) (col V i) - E4 (col U j) (col V o) - E4 (col U o) (col V i)
      + E4 (col U o) (col V o)

theorem R_box {d : ℕ} (o : Fin d) {H K : Mat d} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (htH : H.trace = 0) (htK : K.trace = 0) :
    R H K = ∑ i, ∑ j, (hH.eigenvalues i * hK.eigenvalues j) •
      box hK.eigenvectorUnitary hH.eigenvectorUnitary o i j := by
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
  rw [R_spec hH hK]
  simp only [box, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have z1 : ∑ i, ∑ j, (h i * κ j) • E4 (u j) (v o) = 0 := by
    simp_rw [mul_smul, ← Finset.smul_sum, ← Finset.sum_smul, sh, zero_smul]
  have z2 : ∑ i, ∑ j, (h i * κ j) • E4 (u o) (v i) = 0 := by
    simp_rw [mul_comm (h _), mul_smul, ← Finset.sum_smul, sk, zero_smul, Finset.sum_const_zero]
  have z3 : ∑ i, ∑ j, (h i * κ j) • E4 (u o) (v o) = 0 := by
    simp_rw [mul_comm (h _), mul_smul, ← Finset.sum_smul, sk, zero_smul, Finset.sum_const_zero]
  rw [z1, z2, z3]; simp only [sub_zero, add_zero]; rfl

theorem R_mem {d : ℕ} (hd : 0 < d) {H K : Mat d} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (htH : H.trace = 0) (htK : K.trace = 0) : R H K ∈ L d := by
  rw [R_box ⟨0, hd⟩ hH hK htH htK]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (box_mem _ _ _ i j)

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

def Sm {d : ℕ} (o k l : Fin d) : Mat d :=
  Eu l k + Eu k l - (if k = l then (2:ℂ) • Eu o o else 0)
def Wm {d : ℕ} (k l : Fin d) : Mat d := Complex.I • (Eu l k - Eu k l)
def Am {d : ℕ} (T : Map d) (k l : Fin d) : Mat d := (1/2 : ℂ) • (Φ T k l + Φ T l k)
def Bm {d : ℕ} (T : Map d) (k l : Fin d) : Mat d := (-Complex.I/2) • (Φ T k l - Φ T l k)

theorem T_eq {d : ℕ} (o : Fin d) (T : Map d) (hU : ∀ i j, ∑ k, T (i, j) (k, k) = 0) :
    T = (1/2 : ℝ) • ∑ k, ∑ l, (R (Sm o k l) (Am T k l) + R (Wm k l) (Bm T k l)) := by
  have h3 : ∀ k l, R (Eu l k) (Φ T k l) + R (Eu k l) (Φ T l k) =
      R (Sm o k l) (Am T k l) + R (Wm k l) (Bm T k l) +
        (if k = l then R ((2:ℂ) • Eu o o) (Am T k l) else 0) := by
    intro k l
    ext p q
    split_ifs with hkl
    · simp only [Sm, Wm, Am, Bm, R, hkl, if_true, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul]
      ring_nf; try (rw [Complex.I_sq]; ring)
    · simp only [Sm, Wm, Am, Bm, R, hkl, if_false, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, sub_zero, add_zero]
      ring_nf; try (rw [Complex.I_sq]; ring)
  have h4 : ∑ k, ∑ l, (if k = l then R ((2:ℂ) • Eu o o) (Am T k l) else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ext p q
    simp only [Matrix.sum_apply, R, Am, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Matrix.zero_apply, Φ]
    rw [← Finset.sum_mul]
    have := hU p.1 p.2
    have e : ∑ k, (1/2 : ℂ) * (T (p.1, p.2) (k, k) + T (p.1, p.2) (k, k)) = 0 := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, this]; simp
    rw [e, zero_mul]
  have h2T : (2:ℝ) • T = ∑ k, ∑ l, (R (Sm o k l) (Am T k l) + R (Wm k l) (Bm T k l)) := by
    have e1 := decomp T
    have e2 : T = ∑ k, ∑ l, R (Eu k l) (Φ T l k) := by
      rw [Finset.sum_comm]; exact e1
    have e3 : (2:ℝ) • T = (∑ k, ∑ l, R (Eu l k) (Φ T k l)) + ∑ k, ∑ l, R (Eu k l) (Φ T l k) := by
      rw [two_smul, ← e1, ← e2]
    rw [e3, ← Finset.sum_add_distrib]
    have : ∀ k, (∑ l, R (Eu l k) (Φ T k l)) + ∑ l, R (Eu k l) (Φ T l k) =
        ∑ l, (R (Sm o k l) (Am T k l) + R (Wm k l) (Bm T k l)) +
          ∑ l, (if k = l then R ((2:ℂ) • Eu o o) (Am T k l) else 0) := by
      intro k; rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => h3 k l
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, h4, add_zero]
  rw [← h2T, smul_smul]; norm_num

theorem hΦ {d : ℕ} {T : Map d} (hHP : ∀ i j k l, conj (T (i, j) (k, l)) = T (j, i) (l, k))
    (k l : Fin d) : (Φ T k l)ᴴ = Φ T l k := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Φ, RCLike.star_def, hHP]

theorem Sm_herm {d : ℕ} (o k l : Fin d) : (Sm o k l).IsHermitian := by
  simp only [Sm, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, herm_Eu]
  split_ifs
  · rw [Matrix.conjTranspose_smul, herm_Eu]; simp [add_comm]
  · simp [add_comm]

theorem Sm_trace {d : ℕ} (o k l : Fin d) : (Sm o k l).trace = 0 := by
  simp only [Sm, Matrix.trace_sub, Matrix.trace_add, trace_Eu]
  by_cases h : k = l
  · subst h; simp [trace_Eu, Matrix.trace_smul]; norm_num
  · simp [h, Ne.symm h]

theorem Wm_herm {d : ℕ} (k l : Fin d) : (Wm k l).IsHermitian := by
  simp only [Wm, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, herm_Eu]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, RCLike.star_def, Complex.conj_I]
  ring

theorem Wm_trace {d : ℕ} (k l : Fin d) : (Wm k l).trace = 0 := by
  simp only [Wm, Matrix.trace_smul, Matrix.trace_sub, trace_Eu]
  by_cases h : k = l
  · subst h; simp
  · simp [h, Ne.symm h]

theorem Am_herm {d : ℕ} {T : Map d} (hHP : ∀ i j k l, conj (T (i, j) (k, l)) = T (j, i) (l, k))
    (k l : Fin d) : (Am T k l).IsHermitian := by
  simp only [Am, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    hΦ hHP]
  simp [add_comm]

theorem Bm_herm {d : ℕ} {T : Map d} (hHP : ∀ i j k l, conj (T (i, j) (k, l)) = T (j, i) (l, k))
    (k l : Fin d) : (Bm T k l).IsHermitian := by
  simp only [Bm, Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hΦ hHP]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, RCLike.star_def, map_div₀,
    map_neg, Complex.conj_I, map_ofNat]
  ring

theorem Am_trace {d : ℕ} {T : Map d} (hTP : ∀ k l, ∑ i, T (i, i) (k, l) = 0) (k l : Fin d) :
    (Am T k l).trace = 0 := by
  have tΦ : ∀ k l, (Φ T k l).trace = 0 := fun k l => hTP k l
  simp only [Am, Matrix.trace_smul, Matrix.trace_add, tΦ]; simp

theorem Bm_trace {d : ℕ} {T : Map d} (hTP : ∀ k l, ∑ i, T (i, i) (k, l) = 0) (k l : Fin d) :
    (Bm T k l).trace = 0 := by
  have tΦ : ∀ k l, (Φ T k l).trace = 0 := fun k l => hTP k l
  simp only [Bm, Matrix.trace_smul, Matrix.trace_sub, tΦ]; simp

theorem main_L {d : ℕ} (hd : 0 < d) (T : Map d)
    (hHP : ∀ i j k l, conj (T (i, j) (k, l)) = T (j, i) (l, k))
    (hTP : ∀ k l, ∑ i, T (i, i) (k, l) = 0)
    (hU : ∀ i j, ∑ k, T (i, j) (k, k) = 0) : T ∈ L d := by
  rw [T_eq ⟨0, hd⟩ T hU]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
    Submodule.add_mem _ (R_mem hd (Sm_herm _ _ _) (Am_herm hHP _ _) (Sm_trace _ _ _)
      (Am_trace hTP _ _)) (R_mem hd (Wm_herm _ _) (Bm_herm hHP _ _) (Wm_trace _ _)
      (Bm_trace hTP _ _)))

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


noncomputable section

namespace X6P26T

open QAlgorithms.Papers.Independent.Information100.P26 X6P26C

/-! ### entrywise ℓ¹ bounds -/

def ent1 {d : ℕ} (X : Mat d) : ℝ := ∑ a, ∑ b, ‖X a b‖

def N1 {d : ℕ} (T : Map d) : ℝ := ∑ p, ∑ q, ‖T p q‖

theorem ent1_add_le {d : ℕ} (X Y : Mat d) : ent1 (X + Y) ≤ ent1 X + ent1 Y := by
  unfold ent1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => norm_add_le _ _

theorem ent1_sub_le {d : ℕ} (X Y : Mat d) : ent1 (X - Y) ≤ ent1 X + ent1 Y := by
  unfold ent1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => norm_sub_le _ _

theorem ent1_smul {d : ℕ} (c : ℂ) (X : Mat d) : ent1 (c • X) = ‖c‖ * ent1 X := by
  unfold ent1
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Finset.mul_sum]

theorem ent1_zero {d : ℕ} : ent1 (0 : Mat d) = 0 := by simp [ent1]

theorem ent1_Eu {d : ℕ} (a b : Fin d) : ent1 (Eu a b) = 1 := by
  unfold ent1 Eu
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx; simp [Matrix.single_apply, Ne.symm hx]
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [Matrix.single_apply, Ne.symm hx]
  · simp

theorem ent1_Φ_le {d : ℕ} (T : Map d) (k l : Fin d) : ent1 (Φ T k l) ≤ N1 T := by
  unfold ent1 N1 Φ
  calc ∑ a, ∑ b, ‖T (a, b) (k, l)‖ = ∑ p : Fin d × Fin d, ‖T p (k, l)‖ := by
        rw [Fintype.sum_prod_type]
    _ ≤ ∑ p, ∑ q, ‖T p q‖ := Finset.sum_le_sum fun p _ =>
        Finset.single_le_sum (f := fun q => ‖T p q‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ _)

theorem eig_bound {d : ℕ} {H : Mat d} (hH : H.IsHermitian) (i : Fin d) :
    |hH.eigenvalues i| ≤ ent1 H := by
  rw [hH.eigenvalues_eq i]
  set v := hH.eigenvectorBasis i
  have hv : ∀ a, ‖(v : Fin d → ℂ) a‖ ≤ 1 := by
    intro a
    have h1 := PiLp.norm_apply_le v a
    rw [hH.eigenvectorBasis.orthonormal.1 i] at h1
    exact h1
  refine (RCLike.abs_re_le_norm _).trans ?_
  unfold ent1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have := hv a; have := hv b
  have h0 := norm_nonneg (H a b)
  have h2 := norm_nonneg ((v : Fin d → ℂ) a)
  have h3 := norm_nonneg ((v : Fin d → ℂ) b)
  nlinarith [mul_le_mul_of_nonneg_left (hv b) h0]

theorem ent1_Sm {d : ℕ} (o k l : Fin d) : ent1 (Sm o k l) ≤ 4 := by
  unfold Sm
  refine (ent1_sub_le _ _).trans ?_
  have h1 := ent1_add_le (Eu l k) (Eu k l)
  rw [ent1_Eu, ent1_Eu] at h1
  have h2 : ent1 (if k = l then (2:ℂ) • Eu o o else 0) ≤ 2 := by
    split_ifs
    · rw [ent1_smul, ent1_Eu]; simp
    · rw [ent1_zero]; norm_num
  linarith

theorem ent1_Wm {d : ℕ} (k l : Fin d) : ent1 (Wm k l) ≤ 2 := by
  unfold Wm
  rw [ent1_smul, Complex.norm_I, one_mul]
  have := ent1_sub_le (Eu l k) (Eu k l)
  rw [ent1_Eu, ent1_Eu] at this
  linarith

theorem ent1_Am {d : ℕ} (T : Map d) (k l : Fin d) : ent1 (Am T k l) ≤ N1 T := by
  unfold Am
  rw [ent1_smul]
  have := ent1_add_le (Φ T k l) (Φ T l k)
  have h1 := ent1_Φ_le T k l
  have h2 := ent1_Φ_le T l k
  have : ‖(1/2 : ℂ)‖ = 1/2 := by simp
  rw [this]
  linarith

theorem ent1_Bm {d : ℕ} (T : Map d) (k l : Fin d) : ent1 (Bm T k l) ≤ N1 T := by
  unfold Bm
  rw [ent1_smul]
  have := ent1_sub_le (Φ T k l) (Φ T l k)
  have h1 := ent1_Φ_le T k l
  have h2 := ent1_Φ_le T l k
  have : ‖(-Complex.I/2 : ℂ)‖ = 1/2 := by simp
  rw [this]
  linarith

theorem entry_le_hs {d : ℕ} (T : Map d) (p q : Fin d × Fin d) : ‖T p q‖ ≤ hsNorm T := by
  unfold hsNorm
  rw [Complex.norm_def]
  apply Real.sqrt_le_sqrt
  calc Complex.normSq (T p q) ≤ ∑ q', Complex.normSq (T p q') :=
        Finset.single_le_sum (f := fun q' => Complex.normSq (T p q'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ _)
    _ ≤ ∑ p', ∑ q', Complex.normSq (T p' q') :=
        Finset.single_le_sum (f := fun p' => ∑ q', Complex.normSq (T p' q'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ _)

theorem N1_le {d : ℕ} (T : Map d) : N1 T ≤ (d : ℝ) ^ 4 * hsNorm T := by
  unfold N1
  calc ∑ p, ∑ q, ‖T p q‖ ≤ ∑ _p : Fin d × Fin d, ∑ _q : Fin d × Fin d, hsNorm T :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => entry_le_hs T p q
    _ = (d : ℝ) ^ 4 * hsNorm T := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast; ring

/-! ### the cone of nonnegative combinations of twisted maps -/

def lc2 (d : ℕ) : ((Unitary d × Unitary d) →₀ ℝ) →ₗ[ℝ] Map d :=
  Finsupp.linearCombination ℝ (fun x : Unitary d × Unitary d => beta x.1 x.2)

def Cn (d : ℕ) : Set (Map d) :=
  {X | ∃ f : (Unitary d × Unitary d) →₀ ℝ, (∀ x, 0 ≤ f x) ∧ lc2 d f = X}

theorem Cn_beta {d : ℕ} (U V : Unitary d) (c : ℝ) (hc : 0 ≤ c) : c • beta U V ∈ Cn d := by
  refine ⟨Finsupp.single (U, V) c, fun x => ?_, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> simp [hc]
  · simp [lc2]

theorem Cn_add {d : ℕ} {X Y : Map d} (hX : X ∈ Cn d) (hY : Y ∈ Cn d) : X + Y ∈ Cn d := by
  obtain ⟨f, hf, rfl⟩ := hX
  obtain ⟨g, hg, rfl⟩ := hY
  exact ⟨f + g, fun x => add_nonneg (hf x) (hg x), map_add _ _ _⟩

theorem Cn_zero {d : ℕ} : (0 : Map d) ∈ Cn d := ⟨0, fun _ => le_rfl, map_zero _⟩

theorem Cn_sum {d : ℕ} {ι : Type*} (s : Finset ι) (X : ι → Map d) (h : ∀ i ∈ s, X i ∈ Cn d) :
    ∑ i ∈ s, X i ∈ Cn d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cn_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Cn_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sum_E4_gen {d : ℕ} (U V : Unitary d) :
    ∑ k : Fin d, ∑ j : Fin d, E4 (col U j) (col V k) = (d : ℂ) • depolarizing d := by
  have hU := Matrix.mem_unitaryGroup_iff.1 U.2
  have hV := Matrix.mem_unitaryGroup_iff.1 V.2
  ext p q
  simp only [Matrix.sum_apply, E4, col, Matrix.smul_apply, smul_eq_mul]
  have e1 : ∑ k, ∑ j, (U : Mat d) p.1 j * conj ((U : Mat d) p.2 j) *
      (conj ((V : Mat d) q.1 k) * (V : Mat d) q.2 k) =
      (∑ j, (U : Mat d) p.1 j * star ((U : Mat d) p.2 j)) *
        (∑ k, (V : Mat d) q.2 k * star ((V : Mat d) q.1 k)) := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]; ring
  rw [e1]
  have a1 := congrFun (congrFun hU p.1) p.2
  have a2 := congrFun (congrFun hV q.2) q.1
  rw [Matrix.mul_apply] at a1 a2
  simp only [Matrix.star_apply] at a1 a2
  rw [a1, a2, Matrix.one_apply, Matrix.one_apply, depol_apply]
  have : (d : ℂ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact absurd p.1.isLt (by omega)
    · exact_mod_cast h.ne'
  have h2' : (q.2 = q.1) ↔ (q.1 = q.2) := eq_comm
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;>
    simp [h1, h2, h2', this]

theorem dep_gen {d : ℕ} (hd : 0 < d) (U V : Unitary d) :
    haveI : NeZero d := ⟨hd.ne'⟩
    depolarizing d = ∑ s : Fin d, (1 / d : ℝ) • beta (colPerm U (Equiv.addRight s)) V := by
  haveI : NeZero d := ⟨hd.ne'⟩
  simp only [beta_colPerm, Equiv.coe_addRight]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have : ∀ k : Fin d, ∑ s : Fin d, E4 (col U (k + s)) (col V k) =
      ∑ j : Fin d, E4 (col U j) (col V k) :=
    fun k => Equiv.sum_comp (Equiv.addLeft k) (fun j => E4 (col U j) (col V k))
  rw [Finset.sum_congr rfl fun k _ => this k, sum_E4_gen]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [← Complex.coe_smul, smul_smul]
  push_cast
  rw [one_div, inv_mul_cancel₀ hd', one_smul]

theorem colPerm_zero {d : ℕ} [NeZero d] (U : Unitary d) : colPerm U (Equiv.addRight 0) = U := by
  apply Subtype.ext
  ext a b
  simp [colPerm]

/-- absorb one signed difference into a share of δ -/
theorem piece_pos {d : ℕ} (hd : 0 < d) (M : ℝ) (hM : 0 < M) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ 1 / (M * d)) (U1 V1 U2 V2 : Unitary d) :
    (1 / M) • depolarizing d + c • (beta U1 V1 - beta U2 V2) ∈ Cn d := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have e : (1 / M) • depolarizing d + c • (beta U1 V1 - beta U2 V2) =
      (∑ s : Fin d, (1 / (M * d) - if s = 0 then c else 0) •
        beta (colPerm U2 (Equiv.addRight s)) V2) + c • beta U1 V1 := by
    rw [dep_gen hd U2 V2, Finset.smul_sum]
    simp_rw [smul_smul, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _), colPerm_zero]
    have : 1 / M * (1 / (d : ℝ)) = 1 / (M * d) := by field_simp
    rw [this, smul_sub]
    abel
  rw [e]
  refine Cn_add (Cn_sum _ _ fun s _ => Cn_beta _ _ _ ?_) (Cn_beta _ _ _ hc0)
  split_ifs <;> linarith [show 0 ≤ 1 / (M * d) by positivity]

theorem piece {d : ℕ} (hd : 0 < d) (M : ℝ) (hM : 0 < M) (c : ℝ)
    (hc : |c| ≤ 1 / (M * d)) (U1 V1 U2 V2 : Unitary d) :
    (1 / M) • depolarizing d + c • (beta U1 V1 - beta U2 V2) ∈ Cn d := by
  rcases le_or_gt 0 c with h | h
  · exact piece_pos hd M hM c h (by rwa [abs_of_nonneg h] at hc) _ _ _ _
  · have := piece_pos hd M hM (-c) (by linarith) (by rwa [abs_of_neg h] at hc) U2 V2 U1 V1
    convert this using 2
    rw [neg_smul, ← smul_neg, neg_sub]

theorem box_eq {d : ℕ} (U V : Unitary d) (o i j : Fin d) :
    ∃ P1 P2 N1 N2 : Unitary d, box U V o i j = beta P1 P2 - beta N1 N2 := by
  by_cases hi : i = o
  · subst hi; exact ⟨U, V, U, V, by simp [box]⟩
  by_cases hj : j = o
  · subst hj; exact ⟨U, V, U, V, by simp [box]⟩
  refine ⟨colPerm U (Equiv.swap i j), V, colPerm U (Equiv.swap i j * Equiv.swap o i), V, ?_⟩
  rw [beta_colPerm, beta_colPerm,
    swap_diff (fun k m => E4 (col U m) (col V k)) _ o i (Ne.symm hi)]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)]
  unfold box
  abel

/-! ### from the cone to MTD -/

def ell {d : ℕ} (X : Map d) : ℂ := ∑ i, ∑ k, X (i, i) (k, k)

theorem ell_beta {d : ℕ} (U V : Unitary d) : ell (beta U V) = d := by
  have hU := Matrix.mem_unitaryGroup_iff'.1 U.2
  have hV := Matrix.mem_unitaryGroup_iff'.1 V.2
  unfold ell
  simp only [beta_apply]
  have e : ∀ m : Fin d, (∑ i, (U : Mat d) i m * conj ((U : Mat d) i m)) *
      (∑ k, conj ((V : Mat d) k m) * (V : Mat d) k m) = 1 := by
    intro m
    have a1 := congrFun (congrFun hU m) m
    have a2 := congrFun (congrFun hV m) m
    rw [Matrix.mul_apply] at a1 a2
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at a1 a2
    have b1 : ∑ i, (U : Mat d) i m * conj ((U : Mat d) i m) = 1 := by
      rw [← a1]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [b1, a2, one_mul]
  calc ∑ i, ∑ k, ∑ m, (U : Mat d) i m * conj ((U : Mat d) i m) *
        (conj ((V : Mat d) k m) * (V : Mat d) k m)
      = ∑ m, (∑ i, (U : Mat d) i m * conj ((U : Mat d) i m)) *
          (∑ k, conj ((V : Mat d) k m) * (V : Mat d) k m) := by
        simp only [Finset.sum_mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = d := by simp [e]

theorem ell_t {d : ℕ} (t : Map d) (ht : UnitalChannel t) : ell t = d := by
  unfold ell
  have : ∀ i, ∑ k, t (i, i) (k, k) = 1 := by
    intro i
    have h1 := congrFun (congrFun ht.2 i) i
    rw [applyMap_apply] at h1
    have h2 : ∑ r : Fin d × Fin d, t (i, i) r * (1 : Mat d) r.1 r.2 = ∑ k, t (i, i) (k, k) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Matrix.one_apply, Ne.symm hb]
      · simp
    rw [h2] at h1
    rw [h1]; simp
  simp [this]

theorem ell_sum {d n : ℕ} (p : Fin n → ℝ) (X : Fin n → Map d) :
    ell (∑ j, p j • X j) = ∑ j, (p j : ℂ) * ell (X j) := by
  unfold ell
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem mtd_of_mem {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) (h : t ∈ Cn d) :
    MTD t := by
  classical
  obtain ⟨f, hf, hft⟩ := h
  let e := f.support.equivFin
  have hrep : t = ∑ j, f (e.symm j) • beta (e.symm j).1.1 (e.symm j).1.2 := by
    rw [← hft, lc2, Finsupp.linearCombination_apply, Finsupp.sum,
      ← Finset.sum_coe_sort f.support]
    exact (Equiv.sum_comp e.symm (fun x => f x • beta x.1.1 x.1.2)).symm
  refine ⟨f.support.card, fun j => f (e.symm j), fun j => (e.symm j).1.1,
    fun j => (e.symm j).1.2, fun j => hf _, ?_, hrep⟩
  have h1 := ell_t t ht
  rw [hrep, ell_sum] at h1
  simp only [ell_beta] at h1
  rw [← Finset.sum_mul] at h1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h2 : (∑ j, (f (e.symm j) : ℂ)) = 1 := by
    have := h1
    field_simp at this
    exact this
  exact_mod_cast h2

end X6P26T

open X6P26T X6P26C

namespace QAlgorithms.Papers.Independent.Information100.P26

theorem thm47 {d : ℕ} (hd : 0 < d) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : Map d, UnitalChannel t →
      hsNorm (t - depolarizing d) < e → MTD t := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨1 / (4 * (d : ℝ) ^ 9), by positivity, fun t ht hs => ?_⟩
  apply mtd_of_mem hd t ht
  set o : Fin d := ⟨0, hd⟩
  set T := t - depolarizing d with hTdef
  obtain ⟨hHP, hTP, hU⟩ := props hd t ht
  set M : ℝ := 2 * (d : ℝ) ^ 4 with hMdef
  have hM : 0 < M := by positivity
  have hN : N1 T ≤ (d : ℝ) ^ 4 * hsNorm T := N1_le T
  -- coefficient bound
  have hcoef : ∀ (H K : Mat d) (hH : H.IsHermitian) (hK : K.IsHermitian), ent1 H ≤ 4 →
      ent1 K ≤ N1 T → ∀ i j, |(1/2 : ℝ) * (hH.eigenvalues i * hK.eigenvalues j)| ≤ 1 / (M * d) := by
    intro H K hH hK h1 h2 i j
    have a := (eig_bound hH i).trans h1
    have b := (eig_bound hK j).trans h2
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    have hb : |hK.eigenvalues j| ≤ (d : ℝ) ^ 4 * (1 / (4 * (d : ℝ) ^ 9)) :=
      b.trans (hN.trans (mul_le_mul_of_nonneg_left hs.le (by positivity)))
    have : (1/2 : ℝ) * (|hH.eigenvalues i| * |hK.eigenvalues j|) ≤
        (1/2) * (4 * ((d : ℝ) ^ 4 * (1 / (4 * (d : ℝ) ^ 9)))) := by
      gcongr
    refine this.trans (le_of_eq ?_)
    rw [hMdef]; field_simp; try ring
  -- decomposition
  have hTe := T_eq o T hU
  have hSm := fun k l => Sm_herm o k l
  have hWm := fun k l => Wm_herm (d := d) k l
  have hAm := fun k l => Am_herm hHP k l
  have hBm := fun k l => Bm_herm hHP k l
  have hsplit : ∀ k l, R (Sm o k l) (Am T k l) + R (Wm k l) (Bm T k l) =
      ∑ i, ∑ j, ((hSm k l).eigenvalues i * (hAm k l).eigenvalues j) •
          box (hAm k l).eigenvectorUnitary (hSm k l).eigenvectorUnitary o i j +
        ∑ i, ∑ j, ((hWm k l).eigenvalues i * (hBm k l).eigenvalues j) •
          box (hBm k l).eigenvectorUnitary (hWm k l).eigenvectorUnitary o i j := fun k l => by
    rw [R_box o (hSm k l) (hAm k l) (Sm_trace o k l) (Am_trace hTP k l),
      R_box o (hWm k l) (hBm k l) (Wm_trace k l) (Bm_trace hTP k l)]
  have hδ : depolarizing d = ∑ _k : Fin d, ∑ _l : Fin d, ∑ _i : Fin d, ∑ _j : Fin d,
      ((1 / M) • depolarizing d + (1 / M) • depolarizing d) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← two_smul ℝ,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [hMdef]
    have : (d : ℝ) * ((d : ℝ) * ((d : ℝ) * ((d : ℝ) * (2 * (1 / (2 * (d : ℝ) ^ 4)))))) = 1 := by
      field_simp
    rw [this, one_smul]
  have hTT : T = ∑ k, ∑ l, ∑ i, ∑ j,
      ((1/2 : ℝ) • (((hSm k l).eigenvalues i * (hAm k l).eigenvalues j) •
          box (hAm k l).eigenvectorUnitary (hSm k l).eigenvectorUnitary o i j) +
        (1/2 : ℝ) • (((hWm k l).eigenvalues i * (hBm k l).eigenvalues j) •
          box (hBm k l).eigenvectorUnitary (hWm k l).eigenvectorUnitary o i j)) := by
    rw [hTe]
    simp only [hsplit, Finset.smul_sum, smul_add, Finset.sum_add_distrib]
  have ht' : t = depolarizing d + T := by rw [hTdef]; abel
  rw [ht', hTT]
  nth_rewrite 1 [hδ]
  simp only [← Finset.sum_add_distrib]
  refine Cn_sum _ _ fun k _ => Cn_sum _ _ fun l _ => Cn_sum _ _ fun i _ =>
    Cn_sum _ _ fun j _ => ?_
  obtain ⟨P1, P2, Q1, Q2, hb1⟩ := box_eq (hAm k l).eigenvectorUnitary
    (hSm k l).eigenvectorUnitary o i j
  obtain ⟨P3, P4, Q3, Q4, hb2⟩ := box_eq (hBm k l).eigenvectorUnitary
    (hWm k l).eigenvectorUnitary o i j
  rw [hb1, hb2, smul_smul, smul_smul]
  have c1 := hcoef _ _ (hSm k l) (hAm k l) (ent1_Sm o k l) (ent1_Am T k l) i j
  have c2 := hcoef _ _ (hWm k l) (hBm k l) ((ent1_Wm k l).trans (by norm_num))
    (ent1_Bm T k l) i j
  have e : (1 / M) • depolarizing d + (1 / M) • depolarizing d +
      ((1/2 * ((hSm k l).eigenvalues i * (hAm k l).eigenvalues j)) • (beta P1 P2 - beta Q1 Q2) +
        (1/2 * ((hWm k l).eigenvalues i * (hBm k l).eigenvalues j)) • (beta P3 P4 - beta Q3 Q4)) =
      ((1 / M) • depolarizing d +
          (1/2 * ((hSm k l).eigenvalues i * (hAm k l).eigenvalues j)) • (beta P1 P2 - beta Q1 Q2)) +
        ((1 / M) • depolarizing d +
          (1/2 * ((hWm k l).eigenvalues i * (hBm k l).eigenvalues j)) • (beta P3 P4 - beta Q3 Q4)) := by
    abel
  rw [e]
  exact Cn_add (piece hd M hM _ c1 _ _ _ _) (piece hd M hM _ c2 _ _ _ _)

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : Map d, UnitalChannel t →
      hsNorm (t - depolarizing d) < e → MTD t :=
  thm47 hd

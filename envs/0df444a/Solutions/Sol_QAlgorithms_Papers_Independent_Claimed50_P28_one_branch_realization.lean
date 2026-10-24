-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P28.one_branch_realization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T10:53:31.859286+00:00
-- url     : https://prove2.me/submissions/ef19e248-1744-4a59-bf51-c2a64146eb90

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

-- ===== tw/C1 =====
open scoped BigOperators Matrix Kronecker ComplexConjugate
noncomputable section
namespace X7TW

variable {d : ℕ}

/-- ω = exp(πi/5) -/
def om : ℂ := Complex.exp (Real.pi * Complex.I / 5)

lemma om_ne : om ≠ 0 := Complex.exp_ne_zero _

lemma om_conj : conj om = om⁻¹ := by
  unfold om
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  rw [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring

lemma om_zpow_eq_one {n : ℤ} (h : om ^ n = 1) (hn : -9 ≤ n ∧ n ≤ 9) : n = 0 := by
  unfold om at h
  rw [← Complex.exp_int_mul, Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (n : ℂ) = 10 * k := by
    have h2 : (n : ℂ) * (Real.pi * Complex.I / 5) = (10 * k / 5) * (Real.pi * Complex.I) := by
      rw [hk]; ring
    have h3 : ((n : ℂ) / 5 - 10 * k / 5) * (Real.pi * Complex.I) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linear_combination 5 * h4
    · exact absurd h4 hpi
  have : n = 10 * k := by exact_mod_cast this
  omega

/-- the index weight f_{ij}(x) = [x=i] - [x=j] -/
def wt (i j x : Fin d) : ℤ := (if x = i then 1 else 0) - (if x = j then 1 else 0)

/-- torus element -/
def tor (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal fun x => om ^ wt i j x

lemma om_norm : ‖om‖ = 1 := by
  unfold om; rw [Complex.norm_exp]; simp

lemma conj_om_zpow (n : ℤ) : conj (om ^ n) = om ^ (-n) := by
  rw [map_zpow₀, om_conj, inv_zpow']

lemma tor_mem (i j : Fin d) (hij : i ≠ j) : tor i j ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  refine ⟨?_, ?_⟩
  · unfold tor
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext x
    simp only [Pi.star_apply, Complex.star_def, conj_om_zpow]
    rw [← zpow_add₀ om_ne]; simp
  · unfold tor
    rw [Matrix.det_diagonal]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    rw [Finset.prod_eq_one]
    · simp [wt, Ne.symm hij, hij, zpow_neg, om_ne]
    · intro k hk
      simp only [Finset.mem_erase] at hk
      simp [wt, hk.1, hk.2.1]

lemma comb (a b c e : Fin d)
    (h : ∀ i j : Fin d, i ≠ j → wt i j a + wt i j e = wt i j b + wt i j c) :
    (a = b ∧ e = c) ∨ (a = c ∧ e = b) := by
  by_cases hab : a = b
  · subst hab
    left; refine ⟨rfl, ?_⟩
    by_contra hec
    have := h e c hec
    simp only [wt] at this
    split_ifs at this <;> simp_all
  by_cases hac : a = c
  · subst hac
    right; refine ⟨rfl, ?_⟩
    by_contra heb
    have := h e b heb
    simp only [wt] at this
    split_ifs at this <;> simp_all
  exfalso
  have := h a b hab
  simp only [wt] at this
  split_ifs at this <;> simp_all

/-- Step 1: sparsity of the commutant -/
theorem sparse (N : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hc : ∀ V ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
      N * (V ⊗ₖ V.map conj) = (V ⊗ₖ V.map conj) * N)
    (a b c e : Fin d) (hne : ¬ ((a = b ∧ e = c) ∨ (a = c ∧ e = b))) : N (a, b) (c, e) = 0 := by
  by_contra hN
  apply hne
  apply comb
  intro i j hij
  have h := congrFun (congrFun (hc _ (tor_mem i j hij)) (a, b)) (c, e)
  have hd : tor i j ⊗ₖ (tor i j).map conj =
      Matrix.diagonal fun p : Fin d × Fin d => om ^ (wt i j p.1 - wt i j p.2) := by
    unfold tor
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_kronecker_diagonal]
    congr 1; funext p
    simp only [conj_om_zpow]
    rw [← zpow_add₀ om_ne]; ring_nf
  rw [hd, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : om ^ (wt i j c - wt i j e) = om ^ (wt i j a - wt i j b) := by
    rw [mul_comm (N (a, b) (c, e))] at h
    exact mul_right_cancel₀ hN h
  have h3 : om ^ ((wt i j c - wt i j e) - (wt i j a - wt i j b)) = 1 := by
    rw [zpow_sub₀ om_ne, h2, div_self (zpow_ne_zero _ om_ne)]
  have hb : ∀ x, -1 ≤ wt i j x ∧ wt i j x ≤ 1 := fun x => by
    simp only [wt]; split_ifs <;> omega
  have := om_zpow_eq_one h3 (by
    have := hb a; have := hb b; have := hb c; have := hb e; constructor <;> omega)
  linarith


/-- signed permutation matrix -/
def spm (π : Equiv.Perm (Fin d)) (s : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => if b = π a then s b else 0

lemma right_entry {m : Type*} (π : Equiv.Perm (Fin d)) (s : Fin d → ℂ)
    (M : Matrix m (Fin d × Fin d) ℂ) (p : m) (c e : Fin d) :
    (M * (spm π s ⊗ₖ spm π s)) p (c, e) = M p (π.symm c, π.symm e) * (s c * s e) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π.symm c, π.symm e)]
  · simp [spm, Matrix.kroneckerMap_apply]
  · intro q _ hq
    simp only [spm, Matrix.kroneckerMap_apply, Matrix.of_apply]
    by_cases h1 : c = π q.1
    · by_cases h2 : e = π q.2
      · exfalso; apply hq; rw [h1, h2]; simp
      · simp [h2]
    · simp [h1]
  · simp

lemma left_entry {m : Type*} (π : Equiv.Perm (Fin d)) (s : Fin d → ℂ)
    (M : Matrix (Fin d × Fin d) m ℂ) (a b : Fin d) (r : m) :
    ((spm π s ⊗ₖ spm π s) * M) (a, b) r = s (π a) * s (π b) * M (π a, π b) r := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π a, π b)]
  · simp [spm, Matrix.kroneckerMap_apply]
  · intro q _ hq
    simp only [spm, Matrix.kroneckerMap_apply, Matrix.of_apply]
    by_cases h1 : q.1 = π a
    · by_cases h2 : q.2 = π b
      · exfalso; apply hq; rw [← h1, ← h2]
      · simp [h2]
    · simp [h1]
  · simp

/-- signed swap -/
def sw (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ := spm (Equiv.swap i j) fun k => if k = i then -1 else 1

lemma sw_eq (i j : Fin d) : sw i j =
    (Equiv.swap i j).permMatrix ℂ * Matrix.diagonal fun k => if k = i then -1 else 1 := by
  ext a b
  simp only [sw, spm, Matrix.of_apply, Matrix.mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  by_cases h1 : b = Equiv.swap i j a
  · subst h1; simp
  · rw [if_neg h1, if_neg (Ne.symm h1)]; simp

lemma sw_mem (i j : Fin d) (hij : i ≠ j) : sw i j ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  rw [sw_eq, Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · have hP : (Equiv.swap i j).permMatrix ℂ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
    have hD : (Matrix.diagonal fun k : Fin d => if k = i then (-1 : ℂ) else 1) ∈
        Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k; by_cases h : k = i <;> simp [h]
    exact Submonoid.mul_mem _ hP hD
  · rw [Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal,
      Finset.prod_ite_eq' Finset.univ i]
    simp [Equiv.Perm.sign_swap hij]

lemma sw_conj (i j : Fin d) : (sw i j).map conj = sw i j := by
  ext a b; simp only [sw, spm, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

/-- Step 2 entry identity -/
lemma sw_entry (N : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hc : ∀ V ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
      N * (V ⊗ₖ V.map conj) = (V ⊗ₖ V.map conj) * N)
    (i j : Fin d) (hij : i ≠ j) (a b c e : Fin d) :
    N (a, b) (c, e) * ((if Equiv.swap i j c = i then -1 else 1) * (if Equiv.swap i j e = i then -1 else 1)) =
      (if Equiv.swap i j a = i then -1 else 1) * (if Equiv.swap i j b = i then -1 else 1) *
        N (Equiv.swap i j a, Equiv.swap i j b) (Equiv.swap i j c, Equiv.swap i j e) := by
  have h := congrFun (congrFun (hc _ (sw_mem i j hij)) (a, b)) (Equiv.swap i j c, Equiv.swap i j e)
  rw [sw_conj] at h
  unfold sw at h
  rw [right_entry, left_entry] at h
  simpa [Equiv.swap_apply_self] using h


lemma sgn_sq (b : Prop) [Decidable b] : (if b then (-1 : ℂ) else 1) * (if b then -1 else 1) = 1 := by
  split_ifs <;> norm_num

lemma sgn_ne (b : Prop) [Decidable b] : (if b then (-1 : ℂ) else 1) ≠ 0 := by
  split_ifs <;> norm_num

section comm
variable (N : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hc : ∀ V ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
      N * (V ⊗ₖ V.map conj) = (V ⊗ₖ V.map conj) * N)
include hc

lemma inv_x (i j a b : Fin d) :
    N (a, b) (a, b) = N (Equiv.swap i j a, Equiv.swap i j b) (Equiv.swap i j a, Equiv.swap i j b) := by
  by_cases hij : i = j
  · subst hij; simp
  have h := sw_entry N hc i j hij a b a b
  rw [mul_comm] at h
  exact mul_left_cancel₀ (mul_ne_zero (sgn_ne _) (sgn_ne _)) h

lemma inv_y (i j a c : Fin d) :
    N (a, a) (c, c) = N (Equiv.swap i j a, Equiv.swap i j a) (Equiv.swap i j c, Equiv.swap i j c) := by
  by_cases hij : i = j
  · subst hij; simp
  have h := sw_entry N hc i j hij a a c c
  rw [sgn_sq, sgn_sq, mul_one, one_mul] at h
  exact h

end comm

lemma two_swap (g : Fin d → Fin d → ℂ)
    (hg : ∀ i j a b, g a b = g (Equiv.swap i j a) (Equiv.swap i j b))
    (a b a' b' : Fin d) (hab : a ≠ b) (hab' : a' ≠ b') : g a b = g a' b' := by
  set b1 := Equiv.swap a a' b with hb1
  have h1 : g a b = g a' b1 := by rw [hg a a' a b]; simp [hb1]
  have hb1a : a' ≠ b1 := by
    intro h; apply hab
    have := congrArg (Equiv.swap a a') h
    rwa [Equiv.swap_apply_right, hb1, Equiv.swap_apply_self] at this
  rw [h1, hg b1 b' a' b1]
  rw [Equiv.swap_apply_of_ne_of_ne hb1a hab', Equiv.swap_apply_left]


lemma ext_unitary (hd : 0 < d) (N : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hc : ∀ V ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
      N * (V ⊗ₖ V.map conj) = (V ⊗ₖ V.map conj) * N)
    (V : Matrix (Fin d) (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    N * (V ⊗ₖ V.map conj) = (V ⊗ₖ V.map conj) * N := by
  have hdet : ‖V.det‖ = 1 := by
    have := Matrix.det_of_mem_unitary hV
    exact (CStarRing.norm_of_mem_unitary this)
  have hd0 : V.det ≠ 0 := by intro h; rw [h, norm_zero] at hdet; exact zero_ne_one hdet
  obtain ⟨c, hcd⟩ := IsAlgClosed.exists_pow_nat_eq (V.det)⁻¹ hd
  have hcn : ‖c‖ = 1 := by
    have h1 : ‖c‖ ^ d = 1 := by rw [← norm_pow, hcd, norm_inv, hdet, inv_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hd.ne').mp h1
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hcn]; norm_num
  have hmem : c • V ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hV
      rw [hV, smul_smul, Complex.star_def, hcc, one_smul]
    · rw [Matrix.det_smul, Fintype.card_fin, hcd, inv_mul_cancel₀ hd0]
  have := hc _ hmem
  have e : (c • V) ⊗ₖ (c • V).map conj = V ⊗ₖ V.map conj := by
    have : (c • V).map conj = conj c • V.map conj := by ext a b; simp
    rw [this, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, hcc, one_smul]
  rwa [e] at this

/-- 1/√2 -/
def kap : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma kap_sq : kap * kap = 1 / 2 := by
  unfold kap
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma kap_ne : kap ≠ 0 := by
  unfold kap; simp [Real.sqrt_eq_zero', show ¬ (2:ℝ) ≤ 0 by norm_num]

/-- rotation by 45° in the (i,j)-plane -/
def rot (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun a b =>
  if a = i then (if b = i then kap else if b = j then -kap else 0)
  else if a = j then (if b = i then kap else if b = j then kap else 0)
  else (if b = a then 1 else 0)

lemma rot_conj (i j : Fin d) : (rot i j).map conj = rot i j := by
  ext a b; simp only [rot, Matrix.map_apply, Matrix.of_apply]
  have : conj kap = kap := by unfold kap; rw [Complex.conj_ofReal]
  split_ifs <;> simp [this]

section rotlemmas
variable {i j : Fin d} (hij : i ≠ j)
include hij
lemma rot_ii : rot i j i i = kap := by simp [rot]
lemma rot_ij : rot i j i j = -kap := by simp [rot, Ne.symm hij]
lemma rot_ji : rot i j j i = kap := by simp [rot, Ne.symm hij]
lemma rot_jj : rot i j j j = kap := by simp [rot, Ne.symm hij]
lemma rot_io {k : Fin d} (h1 : k ≠ i) (h2 : k ≠ j) : rot i j i k = 0 := by simp [rot, h1, h2]
lemma rot_jo {k : Fin d} (h1 : k ≠ i) (h2 : k ≠ j) : rot i j j k = 0 := by
  simp [rot, h1, h2, Ne.symm hij]
lemma rot_oo {a : Fin d} (h1 : a ≠ i) (h2 : a ≠ j) (k : Fin d) : rot i j a k = if k = a then 1 else 0 := by
  simp [rot, h1, h2]
end rotlemmas

lemma rot_mem (i j : Fin d) (hij : i ≠ j) : rot i j ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hk : conj kap = kap := by unfold kap; rw [Complex.conj_ofReal]
  have hk2 := kap_sq
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, Complex.star_def]
  -- values of row b at i, j
  have rowb : ∀ b, (b ≠ i ∧ b ≠ j) → rot i j b i = 0 ∧ rot i j b j = 0 := fun b hb => by
    rw [rot_oo hij hb.1 hb.2, rot_oo hij hb.1 hb.2]; simp [Ne.symm hb.1, Ne.symm hb.2]
  by_cases ha : a = i ∨ a = j
  · rw [Finset.sum_eq_add i j hij]
    · rcases ha with ha | ha <;> subst ha
      · by_cases hb1 : b = a
        · subst hb1; simp only [rot_ii hij, rot_ij hij, map_neg, hk, if_pos rfl, if_true]
          linear_combination 2 * hk2
        · by_cases hb2 : b = j
          · subst hb2; simp only [rot_ii hij, rot_ij hij, rot_ji hij, rot_jj hij, map_neg, hk,
              if_neg (Ne.symm hb1)]; ring
          · obtain ⟨h1, h2⟩ := rowb b ⟨hb1, hb2⟩
            rw [h1, h2, if_neg (Ne.symm hb1)]; simp
      · by_cases hb1 : b = a
        · subst hb1; simp only [rot_ji hij, rot_jj hij, map_neg, hk, if_pos rfl, if_true]
          linear_combination 2 * hk2
        · by_cases hb2 : b = i
          · subst hb2; simp only [rot_ii hij, rot_ij hij, rot_ji hij, rot_jj hij, map_neg, hk,
              if_neg (Ne.symm hb1)]; ring
          · obtain ⟨h1, h2⟩ := rowb b ⟨hb2, hb1⟩
            rw [h1, h2, if_neg (Ne.symm hb1)]; simp
    · intro c _ hc
      rcases ha with ha | ha <;> subst ha
      · rw [rot_io hij hc.1 hc.2]; simp
      · rw [rot_jo hij hc.1 hc.2]; simp
    · simp
    · simp
  · push_neg at ha
    rw [Finset.sum_eq_single a]
    · rw [rot_oo hij ha.1 ha.2, if_pos rfl, one_mul]
      by_cases hb1 : b = i
      · subst hb1; rw [rot_io hij ha.1 ha.2, if_neg (by intro h; exact ha.1 h)]; simp
      · by_cases hb2 : b = j
        · subst hb2; rw [rot_jo hij ha.1 ha.2, if_neg (by intro h; exact ha.2 h)]; simp
        · rw [rot_oo hij hb1 hb2]; split_ifs <;> simp_all
    · intro c _ hc
      rw [rot_oo hij ha.1 ha.2, if_neg hc, zero_mul]
    · simp


lemma rot_rel (hd : 0 < d) (N : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hc : ∀ V ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
      N * (V ⊗ₖ V.map conj) = (V ⊗ₖ V.map conj) * N)
    (i j : Fin d) (hij : i ≠ j) :
    N (i, i) (i, i) = N (i, j) (i, j) + N (i, i) (j, j) := by
  have h := congrFun (congrFun (ext_unitary hd N hc (rot i j) (rot_mem i j hij)) (i, i)) (i, j)
  rw [rot_conj, Matrix.mul_apply, Matrix.mul_apply] at h
  have hne : (i, i) ≠ (j, j) := by simp [hij]
  rw [Finset.sum_eq_add (i, i) (j, j) hne, Finset.sum_eq_single (i, j)] at h
  · simp only [Matrix.kroneckerMap_apply, rot_ii hij, rot_ij hij, rot_ji hij, rot_jj hij] at h
    have hk := kap_sq
    have : kap * kap * (N (i, i) (j, j) - N (i, i) (i, i) + N (i, j) (i, j)) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · rw [hk] at h1; norm_num at h1
    · linear_combination -h1
  · intro r _ hr
    rw [sparse N hc r.1 r.2 i j]; · simp
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hij h2.symm
    · exact hr (Prod.ext h1 h2.symm)
  · simp
  · intro r _ hr
    simp only [Matrix.kroneckerMap_apply]
    by_cases h12 : r.1 = r.2
    · have hc1 : r.1 ≠ i := by
        intro h; apply hr.1; exact Prod.ext h (h12 ▸ h)
      have hc2 : r.1 ≠ j := by
        intro h; apply hr.2; exact Prod.ext h (h12 ▸ h)
      rw [rot_oo hij hc1 hc2, if_neg (Ne.symm hc1)]; simp
    · rw [sparse N hc i i r.1 r.2]; · simp
      rintro (⟨_, h2⟩ | ⟨h1, h2⟩)
      · exact h12 h2.symm
      · exact h12 (h1 ▸ h2.symm ▸ rfl)
  · simp
  · simp

/-- Φ = |I>><<I| -/
def Phi (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0

theorem commutant (hd : 2 ≤ d) (N : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hc : ∀ V ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
      N * (V ⊗ₖ V.map conj) = (V ⊗ₖ V.map conj) * N) :
    ∃ x y : ℂ, N = x • 1 + y • Phi d := by
  let i0 : Fin d := ⟨0, by omega⟩
  let j0 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ j0 := by simp [i0, j0, Fin.ext_iff]
  refine ⟨N (i0, j0) (i0, j0), N (i0, i0) (j0, j0), ?_⟩
  have hx := two_swap (fun a b => N (a, b) (a, b)) (fun i j a b => inv_x N hc i j a b)
  have hy := two_swap (fun a c => N (a, a) (c, c)) (fun i j a c => inv_y N hc i j a c)
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Phi, Matrix.of_apply, Prod.mk.injEq,
    smul_eq_mul]
  by_cases h1 : a = b ∧ c = e
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases hac : a = c
    · subst hac
      have hz : N (a, a) (a, a) = N (i0, i0) (i0, i0) := by
        have := inv_y N hc a i0 a a; simpa using this
      rw [hz, rot_rel (by omega) N hc i0 j0 hij]; simp
    · rw [hy a c i0 j0 hac hij]; simp [hac]
  · by_cases h2 : a = c ∧ b = e
    · obtain ⟨rfl, rfl⟩ := h2
      have hab : a ≠ b := fun h => h1 ⟨h, h⟩
      rw [hx a b i0 j0 hab hij]; simp [hab, h1]
    · rw [sparse N hc a b c e]
      · simp [h1, h2]
      · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
        · exact h1 ⟨h3, h4.symm⟩
        · exact h2 ⟨h3, h4.symm⟩

end X7TW

-- ===== tw/C0 =====
open scoped Matrix
noncomputable section
namespace X7TW

abbrev SUg (d : ℕ) := ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)

section cpt
open scoped Matrix.Norms.Elementwise
instance suCompact' (d : ℕ) : CompactSpace (SUg d) := by
  have hc : IsClosed (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
    have : (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) =
        (Matrix.unitaryGroup (Fin d) ℂ : Set _) ∩ {A | A.det = 1} := by
      ext A; simp [Matrix.mem_specialUnitaryGroup_iff]
    rw [this]
    exact isClosed_unitary.inter (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)
  have hb : Bornology.IsBounded
      (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    (show Bornology.IsBounded (Metric.closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1) from
      Metric.isBounded_closedBall).subset (by
      intro U hU
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact entrywise_sup_norm_bound_of_unitary (Matrix.mem_specialUnitaryGroup_iff.mp hU).1)
  exact isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded hc hb)
end cpt

end X7TW

-- ===== tw/C2 =====
open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator
noncomputable section
namespace X7TW

variable {d : ℕ}



/-- K(V) = V ⊗ V̄ -/
def K (V : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := V ⊗ₖ V.map conj

lemma K_mul (A B : Matrix (Fin d) (Fin d) ℂ) : K (A * B) = K A * K B := by
  unfold K; rw [Matrix.map_mul, Matrix.mul_kronecker_mul]

lemma K_ct (A : Matrix (Fin d) (Fin d) ℂ) : (K A)ᴴ = K Aᴴ := by
  unfold K; rw [Matrix.conjTranspose_kronecker]; congr 1

lemma unit_l (V : SUg d) : (V.val)ᴴ * V.val = 1 := by
  have := (Matrix.mem_specialUnitaryGroup_iff.mp V.2).1
  rw [Matrix.mem_unitaryGroup_iff'] at this; exact this

lemma unit_r (V : SUg d) : V.val * (V.val)ᴴ = 1 := by
  have := (Matrix.mem_specialUnitaryGroup_iff.mp V.2).1
  rw [Matrix.mem_unitaryGroup_iff] at this; exact this

lemma K_one : K (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  unfold K; rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_kronecker_one]

def sinv (W : SUg d) : SUg d := ⟨(W.val)ᴴ, by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_l W
  · rw [Matrix.det_conjTranspose, (Matrix.mem_specialUnitaryGroup_iff.mp W.2).2, star_one]⟩

lemma val_cont : Continuous (fun V : SUg d => V.val) := continuous_subtype_val

lemma K_cont : Continuous (fun V : SUg d => K V.val) :=
  continuous_matrix fun p q => by
    simp only [K, Matrix.kroneckerMap_apply, Matrix.map_apply]
    exact (val_cont.matrix_elem _ _).mul (Complex.continuous_conj.comp (val_cont.matrix_elem _ _))

lemma Phi_ct : (Phi d)ᴴ = Phi d := by
  ext p q; simp only [Phi, Matrix.conjTranspose_apply, Matrix.of_apply]; split_ifs <;> simp_all

lemma K_Phi (V : SUg d) : K V.val * Phi d = Phi d := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  have hu := congrFun (congrFun (unit_r V) p1) p2
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hu
  simp only [K, Phi, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  by_cases hq : q1 = q2
  · simp only [hq, and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← hu]; rfl
  · simp [hq]

lemma Phi_K (V : SUg d) : Phi d * K V.val = Phi d := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  have hu := congrFun (congrFun (unit_l V) q2) q1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hu
  simp only [K, Phi, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  by_cases hp : p1 = p2
  · have : (∑ x, V.val x q1 * conj (V.val x q2)) = if q1 = q2 then 1 else 0 := by
      rw [show (if q1 = q2 then (1:ℂ) else 0) = if q2 = q1 then 1 else 0 by simp [eq_comm], ← hu]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm]; rfl
    simp only [hp, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact this
  · simp [hp]

lemma Kct_Phi_K (V : SUg d) : (K V.val)ᴴ * Phi d * K V.val = Phi d := by
  have : (K V.val)ᴴ * Phi d = Phi d := by
    rw [← Phi_ct, ← Matrix.conjTranspose_mul, Phi_K, Phi_ct]
  rw [this, Phi_K]

lemma Phi_trace : (Phi d).trace = d := by
  simp only [Phi, Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type, and_self]
  simp

lemma Phi_sq : Phi d * Phi d = (d : ℂ) • Phi d := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  simp only [Phi, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Fintype.sum_prod_type, smul_eq_mul]
  by_cases hp : p1 = p2 <;> by_cases hq : q1 = q2 <;> simp [hp, hq]

section twirl
variable [MeasurableSpace (SUg d)] [BorelSpace (SUg d)] (μ : Measure (SUg d)) [IsProbabilityMeasure μ]
  (hinv : ∀ (W : SUg d) (f : SUg d → ℂ), Continuous f → ∫ V, f (W * V) ∂μ = ∫ V, f V ∂μ)

/-- entrywise twirl -/
def T2 (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => ∫ V, (K V.val * M * (K V.val)ᴴ) p q ∂μ

omit [MeasurableSpace (SUg d)] [BorelSpace (SUg d)] in
lemma F_cont (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Continuous fun V : SUg d => K V.val * M * (K V.val)ᴴ :=
  (K_cont.matrix_mul continuous_const).matrix_mul K_cont.matrix_conjTranspose

lemma cint {f : SUg d → ℂ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma sandwich_gen {n : Type*} [Fintype n] (F : SUg d → Matrix n n ℂ) (hF : Continuous F)
    (A B : Matrix n n ℂ) :
    A * (Matrix.of fun r s => ∫ V, F V r s ∂μ) * B = Matrix.of fun p q => ∫ V, (A * F V * B) p q ∂μ := by
  ext p q
  simp only [Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun s _ => cint μ (show Continuous fun V => (∑ r, A p r * F V r s) * B s q from
    (continuous_finsetSum _ fun r _ => continuous_const.mul (hF.matrix_elem r s)).mul
      continuous_const))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_mul_const, integral_finsetSum _ (fun r _ => cint μ
    (show Continuous fun V => A p r * F V r s from continuous_const.mul (hF.matrix_elem r s)))]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul]

lemma T2_sandwich (M A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    A * T2 μ M * B = Matrix.of fun p q => ∫ V, (A * (K V.val * M * (K V.val)ᴴ) * B) p q ∂μ :=
  sandwich_gen μ _ (F_cont M) A B

include hinv in
lemma T2_comm (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (W : SUg d) :
    T2 μ M * K W.val = K W.val * T2 μ M := by
  have hKW : K W.val * (K W.val)ᴴ = 1 := by rw [K_ct, ← K_mul, unit_r, K_one]
  have h1 : (K W.val)ᴴ * T2 μ M * K W.val = T2 μ M := by
    rw [T2_sandwich]
    ext p q
    simp only [Matrix.of_apply, T2]
    have := hinv (sinv W) (fun V => (K V.val * M * (K V.val)ᴴ) p q) ((F_cont M).matrix_elem p q)
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    simp only
    have e : (sinv W * V : SUg d).val = (W.val)ᴴ * V.val := rfl
    rw [e, K_mul, ← K_ct, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  calc T2 μ M * K W.val = K W.val * ((K W.val)ᴴ * T2 μ M * K W.val) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKW, Matrix.one_mul]
    _ = K W.val * T2 μ M := by rw [h1]

lemma trace_int {n : Type*} [Fintype n] (G : SUg d → Matrix n n ℂ) (hG : Continuous G) :
    (Matrix.of fun p q => ∫ V, G V p q ∂μ).trace = ∫ V, (G V).trace ∂μ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [integral_finsetSum _ (fun p _ => cint μ (hG.matrix_elem p p))]

lemma T2_trace (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (T2 μ M).trace = M.trace := by
  rw [T2, trace_int μ _ (F_cont M)]
  have : ∀ V : SUg d, (K V.val * M * (K V.val)ᴴ).trace = M.trace := fun V => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, K_ct, ← K_mul, unit_l, K_one, Matrix.one_mul]
  simp only [this, integral_const, probReal_univ, one_smul]

lemma T2_s (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (Phi d * T2 μ M).trace = (Phi d * M).trace := by
  have := T2_sandwich μ M (Phi d) 1
  rw [Matrix.mul_one] at this
  rw [this, trace_int μ _ (((continuous_const.matrix_mul (F_cont M)).matrix_mul continuous_const))]
  have h : ∀ V : SUg d, (Phi d * (K V.val * M * (K V.val)ᴴ) * 1).trace = (Phi d * M).trace := fun V => by
    rw [Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Kct_Phi_K]
  simp only [h, integral_const, probReal_univ, one_smul]

include hinv in
theorem twirl (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    T2 μ M = ((M.trace - (Phi d * M).trace / d) / ((d : ℂ) ^ 2 - 1)) • (1 : Matrix _ _ ℂ) +
      (((Phi d * M).trace - M.trace / d) / ((d : ℂ) ^ 2 - 1)) • Phi d := by
  obtain ⟨x, y, hxy⟩ := commutant hd (T2 μ M) fun V hV => T2_comm μ hinv M ⟨V, hV⟩
  have ht := T2_trace μ M
  have hs := T2_s μ M
  rw [hxy] at ht hs
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, Phi_trace] at ht
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Phi_sq, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Phi_trace] at hs
  simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul, Nat.cast_mul] at ht hs
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (d : ℂ) ^ 2 ≠ 1 := by
      intro h
      have : ((d ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact h
      have := Nat.cast_injective this
      nlinarith
    exact sub_ne_zero.mpr this
  rw [hxy]
  have ex : x = (M.trace - (Phi d * M).trace / d) / ((d : ℂ) ^ 2 - 1) := by
    rw [eq_div_iff hd1, ← ht, ← hs]; field_simp; ring
  have ey : y = ((Phi d * M).trace - M.trace / d) / ((d : ℂ) ^ 2 - 1) := by
    rw [eq_div_iff hd1, ← ht, ← hs]; field_simp; ring
  rw [ex, ey]

end twirl
end X7TW

-- ===== tw/W1 =====
open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator
noncomputable section
namespace X7TW

variable {d : ℕ}

/-- |X>><<X| with row-first vectorization -/
def dy (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => X p.1 p.2 * conj (X q.1 q.2)

lemma conj_entry (U X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    (U * X * Uᴴ) a b = ∑ r : Fin d × Fin d, K U (a, b) r * X r.1 r.2 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, Matrix.kroneckerMap_apply, Matrix.map_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Complex.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

lemma dy_conj (U X : Matrix (Fin d) (Fin d) ℂ) : dy (U * X * Uᴴ) = K U * dy X * (K U)ᴴ := by
  ext p q
  have e1 : dy (U * X * Uᴴ) p q =
      (∑ r, K U p r * X r.1 r.2) * conj (∑ s, K U q s * X s.1 s.2) := by
    simp only [dy, Matrix.of_apply]; rw [conj_entry, conj_entry]
  rw [e1]
  simp only [dy, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Complex.star_def, map_sum,
    map_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

lemma dy_trace (X : Matrix (Fin d) (Fin d) ℂ) : (dy X).trace = ((∑ a, ∑ b, ‖X a b‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dy, Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

lemma diag_sum (f : Fin d × Fin d → ℂ) (h : ∀ p : Fin d × Fin d, p.1 ≠ p.2 → f p = 0) :
    ∑ p, f p = ∑ a, f (a, a) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · intro b _ hb; exact h (a, b) (Ne.symm hb)
  · simp

lemma trPhi (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (Phi d * M).trace = ∑ a, ∑ c, M (c, c) (a, a) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [diag_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [diag_sum]
    · simp [Phi]
    · intro q hq; simp [Phi, hq]
  · intro p hp
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [Phi, hp]

lemma dy_s (X : Matrix (Fin d) (Fin d) ℂ) : (Phi d * dy X).trace = ((‖X.trace‖ ^ 2 : ℝ) : ℂ) := by
  have : (Phi d * dy X).trace = X.trace * conj X.trace := by
    rw [trPhi]
    simp only [dy, Matrix.of_apply, Matrix.trace, Matrix.diag, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
  rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- twirl coefficients -/
def ca (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℂ :=
  (M.trace - (Phi d * M).trace / d) / ((d : ℂ) ^ 2 - 1)
def cb (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℂ :=
  ((Phi d * M).trace - M.trace / d) / ((d : ℂ) ^ 2 - 1)

def swp (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  M.submatrix Prod.swap Prod.swap

lemma swp_trace (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (swp M).trace = M.trace := by
  simp only [swp, Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]; rfl

lemma swp_s (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (Phi d * swp M).trace = (Phi d * M).trace := by
  rw [trPhi, trPhi]; rfl

lemma ca_swp (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ca (swp M) = ca M := by
  simp only [ca, swp_trace, swp_s]
lemma cb_swp (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : cb (swp M) = cb M := by
  simp only [cb, swp_trace, swp_s]

section
variable [MeasurableSpace (SUg d)] [BorelSpace (SUg d)] (μ : Measure (SUg d)) [IsProbabilityMeasure μ]
  (hinv : ∀ (W : SUg d) (f : SUg d → ℂ), Continuous f → ∫ V, f (W * V) ∂μ = ∫ V, f V ∂μ)
include hinv

theorem twirl_entry (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (p q : Fin d × Fin d) :
    ∫ V, (K V.val * M * (K V.val)ᴴ) p q ∂μ = ca M * (if p = q then 1 else 0) + cb M * Phi d p q := by
  have := congrFun (congrFun (twirl μ hinv hd M) p) q
  simp only [T2, Matrix.of_apply] at this
  rw [this]
  simp [ca, cb, Matrix.one_apply]

theorem twirlb_entry (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (p q : Fin d × Fin d) :
    ∫ V, ((V.val.map conj ⊗ₖ V.val) * M * (V.val.map conj ⊗ₖ V.val)ᴴ) p q ∂μ =
      ca M * (if p = q then 1 else 0) + cb M * Phi d p q := by
  have e : ∀ V : SUg d, ((V.val.map conj ⊗ₖ V.val) * M * (V.val.map conj ⊗ₖ V.val)ᴴ) p q =
      (K V.val * swp M * (K V.val)ᴴ) p.swap q.swap := by
    intro V
    have hK : (V.val.map conj ⊗ₖ V.val) = (K V.val).submatrix Prod.swap Prod.swap := by
      ext a b; simp [K, Matrix.kroneckerMap_apply, mul_comm]
    rw [hK]
    have : ((K V.val).submatrix Prod.swap Prod.swap * M * ((K V.val).submatrix Prod.swap Prod.swap)ᴴ) =
        (K V.val * swp M * (K V.val)ᴴ).submatrix Prod.swap Prod.swap := by
      rw [Matrix.conjTranspose_submatrix, swp]
      rw [show M = (M.submatrix Prod.swap Prod.swap).submatrix Prod.swap Prod.swap by ext; rfl]
      rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodComm (Fin d) (Fin d)) _,
        ← Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodComm (Fin d) (Fin d)) _]
      rfl
    rw [this]; rfl
  simp_rw [e]
  rw [twirl_entry μ hinv hd, ca_swp, cb_swp]
  congr 1
  · simp [Prod.swap_inj]
  · simp [Phi, and_comm, eq_comm]

end

def frob (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖ ^ 2

lemma cs_trace (X : Matrix (Fin d) (Fin d) ℂ) : ‖X.trace‖ ^ 2 ≤ d * frob X := by
  have h1 : ‖X.trace‖ ≤ ∑ a, ‖X a a‖ := norm_sum_le _ _
  have h2 : (∑ a, ‖X a a‖) ^ 2 ≤ (Finset.univ : Finset (Fin d)).card * ∑ a, ‖X a a‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ a, ‖X a a‖ ^ 2 ≤ frob X := by
    unfold frob
    refine Finset.sum_le_sum fun a _ => ?_
    exact Finset.single_le_sum (f := fun b => ‖X a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ a)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  calc ‖X.trace‖ ^ 2 ≤ (∑ a, ‖X a a‖) ^ 2 := by gcongr
    _ ≤ d * ∑ a, ‖X a a‖ ^ 2 := h2
    _ ≤ d * frob X := by gcongr

/-- real coefficient on 1-P -/
def ra (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (frob X - ‖X.trace‖ ^ 2 / d) / ((d : ℝ) ^ 2 - 1)
/-- real coefficient on P -/
def rb (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := ‖X.trace‖ ^ 2 / d

lemma ra_nonneg (hd : 2 ≤ d) (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ ra X := by
  unfold ra
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply div_nonneg
  · rw [sub_nonneg, div_le_iff₀ (by linarith)]
    have := cs_trace X; linarith
  · nlinarith

lemma rb_nonneg (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ rb X := by unfold rb; positivity

lemma ca_dy (X : Matrix (Fin d) (Fin d) ℂ) : ca (dy X) = (ra X : ℂ) := by
  unfold ca ra frob
  rw [dy_trace, dy_s]
  push_cast; rfl

lemma cab_dy (hd : 2 ≤ d) (X : Matrix (Fin d) (Fin d) ℂ) :
    ca (dy X) + d * cb (dy X) = (rb X : ℂ) := by
  unfold ca cb rb
  rw [dy_trace, dy_s]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (d : ℂ) ^ 2 ≠ 1 := by
      intro h
      have : ((d ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact h
      have := Nat.cast_injective this
      nlinarith
    exact sub_ne_zero.mpr this
  push_cast
  field_simp
  ring

end X7TW

-- ===== tw/W3 =====
open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator
noncomputable section
namespace X7TW

variable {d : ℕ}

def Pm (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := (d : ℂ)⁻¹ • Phi d
def Qm (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := 1 - Pm d

section
variable [MeasurableSpace (SUg d)] [BorelSpace (SUg d)] (μ : Measure (SUg d)) [IsProbabilityMeasure μ]
  (hinv : ∀ (W : SUg d) (f : SUg d → ℂ), Continuous f → ∫ V, f (W * V) ∂μ = ∫ V, f V ∂μ)
include hinv

theorem wg (hd : 2 ≤ d) (a b c e : Fin d × Fin d) :
    ∫ V, K V.val a b * conj (K V.val c e) ∂μ =
      Pm d a c * Pm d b e + Qm d a c * Qm d b e / ((d : ℂ) ^ 2 - 1) := by
  have h := twirl_entry μ hinv hd (Matrix.single b e (1 : ℂ)) a c
  have e1 : ∀ V : SUg d, (K V.val * Matrix.single b e (1 : ℂ) * (K V.val)ᴴ) a c =
      K V.val a b * conj (K V.val c e) := by
    intro V
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul, Complex.star_def,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp_rw [e1] at h
  rw [h]
  have htr : (Matrix.single b e (1 : ℂ)).trace = if b = e then 1 else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
    by_cases h : b = e
    · subst h; simp
    · simp [h, Ne.symm h]
  have hs : (Phi d * Matrix.single b e (1 : ℂ)).trace = Phi d b e := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp only [Phi, Matrix.of_apply]
    by_cases h1 : e.1 = e.2 <;> by_cases h2 : b.1 = b.2 <;> simp [h1, h2]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (d : ℂ) ^ 2 ≠ 1 := by
      intro h
      have : ((d ^ 2 : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact h
      have := Nat.cast_injective this
      nlinarith
    exact sub_ne_zero.mpr this
  simp only [ca, cb, htr, hs, Pm, Qm, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Weingarten-type kernel -/
def wgv (a b c e : Fin d × Fin d) : ℂ := Pm d a c * Pm d b e + Qm d a c * Qm d b e / ((d : ℂ) ^ 2 - 1)

/-- two-pair conjugation -/
def KK (U V : Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d)) ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  Matrix.of fun p r => K U p.1 r.1 * K V p.2 r.2

omit [BorelSpace (SUg d)] [IsProbabilityMeasure μ] hinv in
lemma KK_entry (U V : Matrix (Fin d) (Fin d) ℂ)
    (M : Matrix ((Fin d × Fin d) × (Fin d × Fin d)) ((Fin d × Fin d) × (Fin d × Fin d)) ℂ) (p q) :
    (KK U V * M * (KK U V)ᴴ) p q = ∑ r, ∑ s, M r s *
      ((K U p.1 r.1 * conj (K U q.1 s.1)) * (K V p.2 r.2 * conj (K V q.2 s.2))) := by
  simp only [Matrix.mul_apply, KK, Matrix.of_apply, Matrix.conjTranspose_apply, Complex.star_def, map_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

theorem dtw (hd : 2 ≤ d)
    (M : Matrix ((Fin d × Fin d) × (Fin d × Fin d)) ((Fin d × Fin d) × (Fin d × Fin d)) ℂ) (p q) :
    ∫ g : SUg d × SUg d, (KK g.1.val g.2.val * M * (KK g.1.val g.2.val)ᴴ) p q ∂(μ.prod μ) =
      ∑ r, ∑ s, M r s * (wgv p.1 r.1 q.1 s.1 * wgv p.2 r.2 q.2 s.2) := by
  have hc : ∀ (a b c e : Fin d × Fin d), Continuous fun V : SUg d => K V.val a b * conj (K V.val c e) :=
    fun a b c e => (K_cont.matrix_elem a b).mul (Complex.continuous_conj.comp (K_cont.matrix_elem c e))
  simp_rw [KK_entry]
  have hint : ∀ r s, Integrable (fun g : SUg d × SUg d => M r s *
      ((K g.1.val p.1 r.1 * conj (K g.1.val q.1 s.1)) * (K g.2.val p.2 r.2 * conj (K g.2.val q.2 s.2))))
      (μ.prod μ) := fun r s =>
    (continuous_const.mul (((hc _ _ _ _).comp continuous_fst).mul ((hc _ _ _ _).comp continuous_snd))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun r _ => integrable_finset_sum _ fun s _ => hint r s)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_finsetSum _ (fun s _ => hint r s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul]
  rw [integral_prod_mul (fun U : SUg d => K U.val p.1 r.1 * conj (K U.val q.1 s.1))
    (fun V : SUg d => K V.val p.2 r.2 * conj (K V.val q.2 s.2))]
  rw [wg μ hinv hd, wg μ hinv hd]
  rfl

end
end X7TW

-- ===== tw/W2 =====

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P28.X7W
open QAlgorithms.Papers.Independent.Claimed50.P28
open X7TW

variable {d : ℕ}

lemma entry {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  exact (L.integral_comp_comm hf).symm

lemma int_psd {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {n : Type*} [Fintype n] [DecidableEq n]
    (f : Y → Matrix n n ℂ) (hf : Integrable f μ) (hp : ∀ y, (f y).PosSemidef) :
    (∫ y, f y ∂μ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, entry _ hf, entry _ hf]
    rw [show star (∫ y, f y j i ∂μ) = conj (∫ y, f y j i ∂μ) from rfl, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have := congrFun (congrFun (hp y).isHermitian i) j
    rw [Matrix.conjTranspose_apply] at this
    exact this
  · let L0 : Matrix n n ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => star v ⬝ᵥ (M *ᵥ v)
        map_add' := fun M N => by simp [Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun c M => by simp [Matrix.smul_mulVec, dotProduct_smul] }
    let L : Matrix n n ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap L0
    have h1 : star v ⬝ᵥ ((∫ y, f y ∂μ) *ᵥ v) = ∫ y, star v ⬝ᵥ (f y *ᵥ v) ∂μ :=
      (L.integral_comp_comm hf).symm
    have hg : ∀ y, star v ⬝ᵥ (f y *ᵥ v) = (((star v ⬝ᵥ (f y *ᵥ v)).re : ℝ) : ℂ) := by
      intro y
      have := ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (hp y)).2 v)
      rw [Complex.nonneg_iff] at this
      apply Complex.ext <;> simp [← this.2]
    rw [h1, integral_congr_ae (Filter.Eventually.of_forall hg), integral_complex_ofReal]
    apply Complex.zero_le_real.mpr
    apply integral_nonneg
    intro y
    have := ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (hp y)).2 v)
    exact (Complex.nonneg_iff.mp this).1

lemma pt_dyad (A' R' : Matrix (Fin d) (Fin d) ℂ) :
    operatorDyad (Matrix.kronecker A' R') = pairedTensor (dy A') (dy R') := by
  ext p q
  simp only [operatorDyad, operatorCoordinates, pairedTensor, dy, Matrix.of_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, map_mul]
  ring

lemma trans_conj (V ρ : Matrix (Fin d) (Fin d) ℂ) :
    (V * ρ * Vᴴ).transpose = V.map conj * ρ.transpose * (V.map conj)ᴴ := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.star_def, Complex.conj_conj, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma K_bar (V : Matrix (Fin d) (Fin d) ℂ) : K (V.map conj) = V.map conj ⊗ₖ V := by
  unfold K; congr 1; ext a b; simp

lemma K_cont' : Continuous (K : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  continuous_matrix fun p q => by
    simp only [K, Matrix.kroneckerMap_apply, Matrix.map_apply]
    exact (continuous_id.matrix_elem _ _).mul (Complex.continuous_conj.comp (continuous_id.matrix_elem _ _))

lemma F_cont' (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) {f : SU d → Matrix (Fin d) (Fin d) ℂ}
    (hf : Continuous f) : Continuous fun V : SU d => K (f V) * M * (K (f V))ᴴ :=
  ((K_cont'.comp hf).matrix_mul continuous_const).matrix_mul (K_cont'.comp hf).matrix_conjTranspose

lemma P_eq (x y : Fin d × Fin d) : maximallyEntangledDensity d x y = (d : ℂ)⁻¹ * Phi d x y := by
  simp only [maximallyEntangledDensity, Phi, Matrix.of_apply]; split_ifs <;> simp

lemma dyad_psd (X : Matrix (ChoiBasis d) (ChoiBasis d) ℂ) : (operatorDyad X).PosSemidef := by
  have : operatorDyad X = Matrix.vecMulVec (operatorCoordinates X) (star (operatorCoordinates X)) := by
    ext p q; simp [operatorDyad, Matrix.vecMulVec_apply]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem main (hd : 2 ≤ d) (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (rho A : Matrix (Fin d) (Fin d) ℂ) :
    (orbitRepresentation haar rho A).PosSemidef ∧
    ∃ g : Fin 4 → ℝ, (∀ j, 0 ≤ g j) ∧
      orbitRepresentation haar rho A = ∑ j, (g j : ℂ) • sector d j := by
  haveI : BorelSpace (SU d) := ⟨rfl⟩
  haveI : IsProbabilityMeasure haar := hhaar.1
  have hinv : ∀ (W : SU d) (f : SU d → ℂ), Continuous f → ∫ V, f (W * V) ∂haar = ∫ V, f V ∂haar := by
    intro W f hf
    have hm : Measurable (fun U : SU d => W * U) := (continuous_const.mul continuous_id).measurable
    conv_rhs => rw [← (hhaar.2 W).map_eq]
    rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  set G : GroupPair d → Matrix (ChoiBasis d × ChoiBasis d) (ChoiBasis d × ChoiBasis d) ℂ :=
    fun g => operatorDyad (Matrix.kronecker
      ((g.1 : Matrix (Fin d) (Fin d) ℂ) * A * (g.1 : Matrix (Fin d) (Fin d) ℂ)ᴴ)
      (((g.2 : Matrix (Fin d) (Fin d) ℂ) * rho * (g.2 : Matrix (Fin d) (Fin d) ℂ)ᴴ).transpose)) with hGdef
  have hval : Continuous (fun V : SU d => (V : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  have hvalb : Continuous (fun V : SU d => (V : Matrix (Fin d) (Fin d) ℂ).map conj) :=
    hval.matrix_map Complex.continuous_conj
  have hG : ∀ g : GroupPair d, G g = pairedTensor (K g.1.val * dy A * (K g.1.val)ᴴ)
      (K (g.2.val.map conj) * dy rho.transpose * (K (g.2.val.map conj))ᴴ) := by
    intro g
    simp only [hGdef]
    rw [pt_dyad, dy_conj, trans_conj, dy_conj]
  have hGc : Continuous G := by
    have : G = fun g => pairedTensor (K g.1.val * dy A * (K g.1.val)ᴴ)
        (K (g.2.val.map conj) * dy rho.transpose * (K (g.2.val.map conj))ᴴ) := funext hG
    rw [this]
    refine continuous_matrix fun p q => ?_
    simp only [pairedTensor]
    exact (((F_cont' (dy A) hval).comp continuous_fst).matrix_elem _ _).mul
      (((F_cont' (dy rho.transpose) hvalb).comp continuous_snd).matrix_elem _ _)
  have hGi : Integrable G (haar.prod haar) :=
    hGc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the decomposition
  set a1 := ra A; set b1 := rb A; set a2 := ra rho.transpose; set b2 := rb rho.transpose
  have hdec : orbitRepresentation haar rho A =
      ∑ j, ((![b1 * b2, a1 * b2, b1 * a2, a1 * a2] : Fin 4 → ℝ) j : ℂ) • sector d j := by
    ext p q
    rw [orbitRepresentation, entry _ hGi]
    simp_rw [hG]
    simp only [pairedTensor]
    rw [integral_prod_mul (fun U : SU d => (K U.val * dy A * (K U.val)ᴴ) (p.1.1, p.2.1) (q.1.1, q.2.1))
      (fun V : SU d => (K (V.val.map conj) * dy rho.transpose * (K (V.val.map conj))ᴴ)
        (p.1.2, p.2.2) (q.1.2, q.2.2))]
    simp_rw [K_bar]
    rw [twirl_entry haar hinv hd, twirlb_entry haar hinv hd]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have e1 := ca_dy A
    have e2 := cab_dy hd A
    have e3 := ca_dy rho.transpose
    have e4 := cab_dy hd rho.transpose
    have f2 : cb (dy A) = ((b1 : ℂ) - a1) / d := by
      rw [eq_div_iff hd0]; linear_combination e2 - e1
    have f4 : cb (dy rho.transpose) = ((b2 : ℂ) - a2) / d := by
      rw [eq_div_iff hd0]; linear_combination e4 - e3
    rw [e1, e3, f2, f4]
    simp only [Fin.sum_univ_four, Matrix.add_apply, Matrix.smul_apply, sector, pairedTensor,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Matrix.sub_apply, Matrix.one_apply, P_eq, smul_eq_mul]
    push_cast
    field_simp
    ring
  refine ⟨?_, ⟨![b1 * b2, a1 * b2, b1 * a2, a1 * a2], ?_, hdec⟩⟩
  · rw [orbitRepresentation]
    refine int_psd G hGi fun g => ?_
    simp only [hGdef]
    exact dyad_psd _
  · have h1 := ra_nonneg hd A; have h2 := rb_nonneg A
    have h3 := ra_nonneg hd rho.transpose; have h4 := rb_nonneg rho.transpose
    intro j; fin_cases j <;> simp <;> positivity

end QAlgorithms.Papers.Independent.Claimed50.P28.X7W

-- ===== p28b/B1 =====

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P28.X7B
open QAlgorithms.Papers.Independent.Claimed50.P28
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open X7TW

variable {d : ℕ}

lemma be_entry (U : SU d) (k a b : Fin d) :
    branchEffect U k a b = conj ((U : Op (Fin d)) k a) * (U : Op (Fin d)) k b := by
  simp only [branchEffect, QAlgorithms.pureDensity, QAlgorithms.ket, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, EuclideanSpace.single_apply, Complex.star_def]
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  simp

lemma tr_be (U : SU d) (k : Fin d) (M : Op (Fin d)) :
    (branchEffect U k * M).trace = ∑ a, ∑ b, M b a * (X7TW.K (U : Op (Fin d)) (k, k) (b, a)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, be_entry, X7TW.K, Matrix.kroneckerMap_apply,
    Matrix.map_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma be_K (U : SU d) (k p q : Fin d) :
    branchEffect U k p q = conj (X7TW.K (U : Op (Fin d)) (k, k) (p, q)) := by
  rw [be_entry]
  simp only [X7TW.K, Matrix.kroneckerMap_apply, Matrix.map_apply, map_mul, Complex.conj_conj]

lemma Ucont : Continuous fun U : SU d => (U : Op (Fin d)) := continuous_subtype_val

lemma Kc (a b : Fin d × Fin d) : Continuous fun U : SU d => X7TW.K (U : Op (Fin d)) a b := by
  simp only [X7TW.K, Matrix.kroneckerMap_apply, Matrix.map_apply]
  exact (Ucont.matrix_elem _ _).mul (Complex.continuous_conj.comp (Ucont.matrix_elem _ _))

lemma cint' (haar : Measure (SU d)) [IsProbabilityMeasure haar] {f : SU d → ℂ} (hf : Continuous f) :
    Integrable f haar := by
  haveI : BorelSpace (SU d) := ⟨rfl⟩
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mom2 (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar) (hd : 2 ≤ d) (M : Op (Fin d)) (p q : Fin d) :
    ∫ U, ∑ k, (branchEffect U k * M).trace * branchEffect U k p q ∂haar =
      (M.trace * (if p = q then 1 else 0) + M p q) / ((d : ℂ) + 1) := by
  haveI : BorelSpace (SU d) := ⟨rfl⟩
  haveI : IsProbabilityMeasure haar := hhaar.1
  have hinv : ∀ (W : SU d) (f : SU d → ℂ), Continuous f → ∫ V, f (W * V) ∂haar = ∫ V, f V ∂haar := by
    intro W f hf
    have hm : Measurable (fun U : SU d => W * U) := (continuous_const.mul continuous_id).measurable
    conv_rhs => rw [← (hhaar.2 W).map_eq]
    rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  have hI : ∀ k a b : Fin d, Integrable (fun U : SU d => M b a * (X7TW.K (U : Op (Fin d)) (k, k) (b, a) *
      conj (X7TW.K (U : Op (Fin d)) (k, k) (p, q)))) haar :=
    fun k a b => (cint' haar ((Kc _ _).mul (Complex.continuous_conj.comp (Kc _ _)))).const_mul _
  have e : ∀ U : SU d, ∑ k, (branchEffect U k * M).trace * branchEffect U k p q =
      ∑ k, ∑ a, ∑ b, M b a * (X7TW.K (U : Op (Fin d)) (k, k) (b, a) *
        conj (X7TW.K (U : Op (Fin d)) (k, k) (p, q))) := by
    intro U
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tr_be, be_K, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [e]
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hI k a b]
  simp_rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hI _ a b]
  simp_rw [integral_finset_sum _ fun b _ => hI _ _ b, integral_const_mul]
  have hW := fun k a b => X7TW.wg haar hinv hd (k, k) (b, a) (k, k) (p, q)
  simp only [hW]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (show d + 1 ≠ 0 by omega)
  have hd2 : (d : ℂ) ^ 2 - 1 = ((d : ℂ) - 1) * ((d : ℂ) + 1) := by ring
  have hd3 : (d : ℂ) - 1 ≠ 0 := by
    have : (d : ℂ) ≠ 1 := by exact_mod_cast (show d ≠ 1 by omega)
    exact sub_ne_zero.mpr this
  simp only [X7TW.Pm, X7TW.Qm, X7TW.Phi, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul, Prod.mk.injEq, and_self, if_true]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [mul_div_assoc', mul_sub, sub_div, Finset.sum_sub_distrib, ← Finset.sum_div, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero,
    ← Finset.sum_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.trace, Matrix.diag]
  rw [hd2]
  split_ifs <;> field_simp <;> ring

end QAlgorithms.Papers.Independent.Claimed50.P28.X7B

-- ===== p28b/B2 =====

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P28.X7B
open QAlgorithms.Papers.Independent.Claimed50.P28
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

variable {d : ℕ}

lemma unitL (U : SU d) : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := by
  have := (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  rw [Matrix.mem_unitaryGroup_iff'] at this; exact this

lemma unitR (U : SU d) : (U : Op (Fin d)) * (U : Op (Fin d))ᴴ = 1 := by
  have := (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  rw [Matrix.mem_unitaryGroup_iff] at this; exact this

lemma pk_entry (k a b : Fin d) :
    QAlgorithms.pureDensity (QAlgorithms.ket k) a b = if a = k ∧ b = k then 1 else 0 := by
  simp only [QAlgorithms.pureDensity, QAlgorithms.ket, Matrix.of_apply, EuclideanSpace.single_apply]
  by_cases h1 : a = k <;> by_cases h2 : b = k <;> simp [h1, h2]

lemma pk_mul (k l : Fin d) : QAlgorithms.pureDensity (QAlgorithms.ket k) * QAlgorithms.pureDensity (QAlgorithms.ket l) =
    if k = l then QAlgorithms.pureDensity (QAlgorithms.ket k) else 0 := by
  ext a b
  simp only [Matrix.mul_apply, pk_entry]
  by_cases h : k = l
  · subst h; simp only [if_true]
    rw [pk_entry]
    by_cases h1 : a = k <;> by_cases h2 : b = k <;> simp [h1, h2]
  · simp only [h, if_false, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : x = k <;> simp [h1, h]

lemma pk_ct (k : Fin d) : (QAlgorithms.pureDensity (QAlgorithms.ket k))ᴴ = QAlgorithms.pureDensity (QAlgorithms.ket k) := by
  ext a b
  rw [Matrix.conjTranspose_apply, pk_entry, pk_entry]
  by_cases h1 : a = k <;> by_cases h2 : b = k <;> simp [h1, h2]

lemma pk_sum : ∑ k : Fin d, QAlgorithms.pureDensity (QAlgorithms.ket k) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, pk_entry, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, if_false]
    exact Finset.sum_eq_zero fun x _ => if_neg (fun hx => h (hx.1.trans hx.2.symm))

lemma sumB (U : SU d) : ∑ k, branchEffect U k = 1 := by
  simp only [branchEffect, ← Finset.sum_mul, ← Finset.mul_sum, pk_sum, Matrix.mul_one, unitL]

lemma trB (U : SU d) (k : Fin d) : (branchEffect U k).trace = 1 := by
  rw [branchEffect, Matrix.trace_mul_comm, ← Matrix.mul_assoc, unitR, Matrix.one_mul]
  simp [Matrix.trace, pk_entry]

lemma trsum (U : SU d) (M : Op (Fin d)) : ∑ k, (branchEffect U k * M).trace = M.trace := by
  rw [← Matrix.trace_sum, ← Finset.sum_mul, sumB, Matrix.one_mul]

lemma B_cont (k : Fin d) : Continuous fun U : SU d => branchEffect U k :=
  (Ucont.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul Ucont

lemma F_cont (M : Op (Fin d)) :
    Continuous fun U : SU d => ∑ k, (branchEffect U k * M).trace • branchDual U k := by
  refine continuous_finset_sum _ fun k _ => ?_
  have h1 : Continuous fun U : SU d => (branchEffect U k * M).trace :=
    ((B_cont k).matrix_mul continuous_const).matrix_trace
  have h2 : Continuous fun U : SU d => branchDual U k := by
    unfold branchDual
    exact ((continuous_const (y := ((d : ℂ) + 1))).smul (B_cont k)).sub continuous_const
  exact h1.smul h2

lemma su1 (U : SU 1) : (U : Op (Fin 1)) = 1 := by
  have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2
  rw [Matrix.det_fin_one] at h
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, h]; rfl

theorem frame (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar) (hd : 0 < d) (M : Op (Fin d)) :
    (∫ U, ∑ k, (branchEffect U k * M).trace • branchDual U k ∂haar) = M := by
  haveI : BorelSpace (SU d) := ⟨rfl⟩
  haveI : IsProbabilityMeasure haar := hhaar.1
  have hint : Integrable (fun U : SU d => ∑ k, (branchEffect U k * M).trace • branchDual U k) haar :=
    (F_cont M).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  ext p q
  rw [X7W.entry _ hint]
  have e : ∀ U : SU d, (∑ k, (branchEffect U k * M).trace • branchDual U k) p q =
      ((d : ℂ) + 1) * ∑ k, (branchEffect U k * M).trace * branchEffect U k p q -
        (if p = q then 1 else 0) * M.trace := by
    intro U
    rw [← trsum U M]
    simp only [Matrix.sum_apply, Matrix.smul_apply, branchDual, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [e]
  rcases Nat.lt_or_ge d 2 with h1 | h2
  · obtain rfl : d = 1 := by omega
    have hp : p = q := Subsingleton.elim _ _
    subst hp
    have hB : ∀ U : SU 1, branchEffect U 0 = 1 := by
      intro U
      rw [branchEffect, su1 U, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      ext a b
      rw [pk_entry, Subsingleton.elim a 0, Subsingleton.elim b 0]; simp
    simp only [Fin.sum_univ_one, hB, Matrix.one_mul, if_true, one_mul, integral_const, probReal_univ, one_smul,
      Matrix.one_apply_eq]
    rw [Subsingleton.elim p 0]
    simp [Matrix.trace]
    ring
  · have hi1 : Integrable (fun U : SU d => ((d : ℂ) + 1) * ∑ k, (branchEffect U k * M).trace * branchEffect U k p q)
        haar := by
      refine (cint' haar ?_).const_mul _
      exact continuous_finset_sum _ fun k _ =>
        (((B_cont k).matrix_mul continuous_const).matrix_trace).mul ((B_cont k).matrix_elem p q)
    rw [integral_sub hi1 (integrable_const _), integral_const_mul, mom2 haar hhaar h2 M p q]
    simp only [integral_const, probReal_univ, one_smul]
    have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (show d + 1 ≠ 0 by omega)
    field_simp
    split_ifs <;> ring

end QAlgorithms.Papers.Independent.Claimed50.P28.X7B

-- ===== p28b/B3 =====

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P28.X7B
open QAlgorithms.Papers.Independent.Claimed50.P28
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

variable {d : ℕ}

lemma pk_psd (k : Fin d) : (QAlgorithms.pureDensity (QAlgorithms.ket k)).PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self (QAlgorithms.pureDensity (QAlgorithms.ket k))
  rwa [pk_ct, pk_mul, if_pos rfl] at this

lemma B_psd (U : SU d) (k : Fin d) : (branchEffect U k).PosSemidef :=
  (pk_psd k).conjTranspose_mul_mul_same _

lemma B_mul (U : SU d) (k l : Fin d) : branchEffect U k * branchEffect U l =
    if k = l then branchEffect U k else 0 := by
  simp only [branchEffect]
  have : (U : Op (Fin d))ᴴ * QAlgorithms.pureDensity (QAlgorithms.ket k) * (U : Op (Fin d)) *
      ((U : Op (Fin d))ᴴ * QAlgorithms.pureDensity (QAlgorithms.ket l) * (U : Op (Fin d))) =
      (U : Op (Fin d))ᴴ * (QAlgorithms.pureDensity (QAlgorithms.ket k) * QAlgorithms.pureDensity (QAlgorithms.ket l)) *
        (U : Op (Fin d)) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Op (Fin d)) (U : Op (Fin d))ᴴ, unitR, Matrix.one_mul]
  rw [this, pk_mul]
  split_ifs <;> simp

/-- Tr(E B_k) as a quadratic form -/
lemma tr_EB (U : SU d) (k : Fin d) (E : Op (Fin d)) :
    (E * branchEffect U k).trace = star (fun a => conj ((U : Op (Fin d)) k a)) ⬝ᵥ
      (E *ᵥ (fun a => conj ((U : Op (Fin d)) k a))) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, be_entry, dotProduct, Matrix.mulVec, Pi.star_apply,
    Complex.star_def, Complex.conj_conj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma tr_EB_nonneg (U : SU d) (k : Fin d) (E : Op (Fin d)) (hE : E.PosSemidef) :
    0 ≤ (E * branchEffect U k).trace := by
  rw [tr_EB]
  exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hE).2 _

theorem main (hd : 0 < d) (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar) :
    (∀ U : SU d, (∀ k, (branchEffect U k).PosSemidef ∧
      branchEffect U k * branchEffect U k = branchEffect U k) ∧
      (∀ k l, k ≠ l → branchEffect U k * branchEffect U l = 0) ∧
      ∑ k, branchEffect U k = 1) ∧
    (∀ rho : Op (Fin d), QAlgorithms.IsDensityMatrix rho →
      (∫ U, ∑ k, (branchEffect U k * rho).trace • branchDual U k ∂haar) = rho) ∧
    (∀ (J : Type) [Fintype J] (E : J → Op (Fin d)),
      (∀ j, (E j).PosSemidef) → (∑ j, E j) = 1 →
      (∀ U k j, 0 ≤ branchPOVMProbability E U k j) ∧
      (∀ U, ∑ k, ∑ j, branchPOVMProbability E U k j = 1) ∧
      (∀ j, (∫ U, ∑ k, ((d : ℂ) * (branchPOVMProbability E U k j : ℂ)) •
        branchDual U k ∂haar) = E j)) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨fun U => ⟨fun k => ⟨B_psd U k, by rw [B_mul, if_pos rfl]⟩,
    fun k l hkl => by rw [B_mul, if_neg hkl], sumB U⟩, fun rho _ => frame haar hhaar hd rho, ?_⟩
  intro J _ E hE hsum
  have hreal : ∀ U k j, (((E j * branchEffect U k).trace.re : ℝ) : ℂ) = (E j * branchEffect U k).trace := by
    intro U k j
    have h := tr_EB_nonneg U k (E j) (hE j)
    rw [Complex.nonneg_iff] at h
    apply Complex.ext <;> simp [← h.2]
  refine ⟨fun U k j => ?_, fun U => ?_, fun j => ?_⟩
  · unfold branchPOVMProbability
    have h := tr_EB_nonneg U k (E j) (hE j)
    rw [Complex.nonneg_iff] at h
    exact div_nonneg h.1 (Nat.cast_nonneg d)
  · unfold branchPOVMProbability
    have : ∀ k, ∑ j, (E j * branchEffect U k).trace.re / (d : ℝ) = 1 / d := by
      intro k
      rw [← Finset.sum_div, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hsum, Matrix.one_mul, trB]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · have e : ∀ U k, ((d : ℂ) * (branchPOVMProbability E U k j : ℂ)) = (branchEffect U k * E j).trace := by
      intro U k
      unfold branchPOVMProbability
      push_cast
      rw [hreal, Matrix.trace_mul_comm]
      field_simp
    simp_rw [e]
    exact frame haar hhaar hd (E j)

end QAlgorithms.Papers.Independent.Claimed50.P28.X7B

namespace QAlgorithms.Papers.Independent.Claimed50.P28
end QAlgorithms.Papers.Independent.Claimed50.P28

open QAlgorithms.Papers.Independent.Claimed50.P28 in
open QAlgorithms.Papers.Independent.Information100.P21 (Op) in
theorem solution {d : ℕ} (hd : 0 < d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar) :
    (∀ U : SU d, (∀ k, (branchEffect U k).PosSemidef ∧
      branchEffect U k * branchEffect U k = branchEffect U k) ∧
      (∀ k l, k ≠ l → branchEffect U k * branchEffect U l = 0) ∧
      ∑ k, branchEffect U k = 1) ∧
    (∀ rho : Op (Fin d), QAlgorithms.IsDensityMatrix rho →
      (∫ U, ∑ k, (branchEffect U k * rho).trace • branchDual U k ∂haar) = rho) ∧
    (∀ (J : Type) [Fintype J] (E : J → Op (Fin d)),
      (∀ j, (E j).PosSemidef) → (∑ j, E j) = 1 →
      (∀ U k j, 0 ≤ branchPOVMProbability E U k j) ∧
      (∀ U, ∑ k, ∑ j, branchPOVMProbability E U k j = 1) ∧
      (∀ j, (∫ U, ∑ k, ((d : ℂ) * (branchPOVMProbability E U k j : ℂ)) •
        branchDual U k ∂haar) = E j)) :=
  QAlgorithms.Papers.Independent.Claimed50.P28.X7B.main hd haar hhaar

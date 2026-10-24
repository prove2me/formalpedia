-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P21.covarianceReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T11:19:22.987629+00:00
-- url     : https://prove2.me/submissions/3e618320-1be6-427f-adb4-5fbb6f91795f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21

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

-- ===== P21CovNorm =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7P21
open QAlgorithms.Papers.Independent.Claimed50.P21

instance suCompact (d : ℕ) : CompactSpace (SU d) := by
  suffices h : IsCompact (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) from
    isCompact_iff_compactSpace.mp h
  have h1 : IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (Matrix.unitaryGroup (Fin d) ℂ)))
  have h2 : IsClosed {A : Matrix (Fin d) (Fin d) ℂ | A.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  have : (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) =
      (Matrix.unitaryGroup (Fin d) ℂ : Set _) ∩ {A | A.det = 1} := by
    ext A; simp [Matrix.mem_specialUnitaryGroup_iff]
  rw [this]; exact h1.inter_right h2

lemma int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma entry {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm

lemma int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m] [DecidableEq m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

variable {d : ℕ}

lemma val_cont : Continuous (fun V : SU d => unitaryMatrix V) := continuous_subtype_val

lemma integrable_of_cont {E : Type*} [NormedAddCommGroup E] (H : HaarLaw d) {f : SU d → E}
    (hf : Continuous f) : Integrable f H.law := by
  haveI := H.probability
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma unit_left (W : SU d) : (unitaryMatrix W)ᴴ * unitaryMatrix W = 1 := by
  have := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).1
  rw [Matrix.mem_unitaryGroup_iff'] at this; exact this

lemma unit_right (W : SU d) : unitaryMatrix W * (unitaryMatrix W)ᴴ = 1 := by
  have := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).1
  rw [Matrix.mem_unitaryGroup_iff] at this; exact this

def sinv (W : SU d) : SU d := ⟨(unitaryMatrix W)ᴴ, by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_left W
  · rw [Matrix.det_conjTranspose]
    have := (Matrix.mem_specialUnitaryGroup_iff.mp W.2).2
    simp only [unitaryMatrix] at *; rw [this, star_one]⟩

lemma int_left (H : HaarLaw d) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SU d → E) (hf : Continuous f) (W : SU d) :
    ∫ V, f (W * V) ∂H.law = ∫ V, f V ∂H.law := by
  have hm : Measurable (fun U : SU d => W * U) := (continuous_const.mul continuous_id).measurable
  conv_rhs => rw [← H.left_invariant W]
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]

def M1 (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∫ V, unitaryMatrix V * X * (unitaryMatrix V)ᴴ ∂H.law

lemma M1_cont (X : Matrix (Fin d) (Fin d) ℂ) :
    Continuous fun V : SU d => unitaryMatrix V * X * (unitaryMatrix V)ᴴ :=
  (val_cont.matrix_mul continuous_const).matrix_mul val_cont.matrix_conjTranspose

lemma M1_inv (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) (W : SU d) :
    (unitaryMatrix W)ᴴ * M1 H X * unitaryMatrix W = M1 H X := by
  unfold M1
  rw [← int_conj _ _ _ (integrable_of_cont H (M1_cont X))]
  rw [← int_left H _ (M1_cont X) (sinv W)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only
  have : unitaryMatrix (sinv W * V) = (unitaryMatrix W)ᴴ * unitaryMatrix V := rfl
  rw [this, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

lemma M1_comm (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) (W : SU d) :
    M1 H X * unitaryMatrix W = unitaryMatrix W * M1 H X := by
  have h := M1_inv H X W
  calc M1 H X * unitaryMatrix W = unitaryMatrix W * ((unitaryMatrix W)ᴴ * M1 H X * unitaryMatrix W) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_right, Matrix.one_mul]
    _ = unitaryMatrix W * M1 H X := by rw [h]

/-- diagonal special unitary with phases i, -i at positions i, j. -/
def Dg (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun k => if k = i then Complex.I else if k = j then -Complex.I else 1

lemma Dg_mem (i j : Fin d) (hij : i ≠ j) : Dg i j ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  refine ⟨?_, ?_⟩
  · unfold Dg
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext k
    by_cases h : k = i
    · simp [h]
    · by_cases h' : k = j
      · subst h'; simp [h]
      · simp [h, h']
  · unfold Dg
    rw [Matrix.det_diagonal]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    rw [Finset.prod_eq_one]
    · simp [Ne.symm hij]
    · intro k hk
      simp only [Finset.mem_erase] at hk
      simp [hk.1, hk.2.1]

/-- signed transposition. -/
def Sw (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  (Equiv.swap i j).permMatrix ℂ * Matrix.diagonal fun k => if k = i then -1 else 1

lemma Sw_mem (i j : Fin d) (hij : i ≠ j) : Sw i j ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  refine ⟨?_, ?_⟩
  · have hP : (Equiv.swap i j).permMatrix ℂ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
    have hD : (Matrix.diagonal fun k : Fin d => if k = i then (-1 : ℂ) else 1) ∈
        Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k; by_cases h : k = i <;> simp [h]
    have := Submonoid.mul_mem _ hP hD
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
    exact this
  · rw [Sw, Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal,
      Finset.prod_ite_eq' Finset.univ i]
    simp [Equiv.Perm.sign_swap hij]


lemma M1_offdiag (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (hij : i ≠ j) :
    M1 H X i j = 0 := by
  have h := congrFun (congrFun (M1_comm H X ⟨Dg i j, Dg_mem i j hij⟩) i) j
  simp only [unitaryMatrix, Dg, Matrix.mul_diagonal, Matrix.diagonal_mul, Ne.symm hij, if_false, if_true] at h
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp
  have : (2 * Complex.I) * M1 H X i j = 0 := by linear_combination -h
  simpa [hI] using this

lemma M1_diag (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    M1 H X i i = M1 H X j j := by
  by_cases hij : i = j
  · rw [hij]
  have h := congrFun (congrFun (M1_comm H X ⟨Sw i j, Sw_mem i j hij⟩) i) j
  simp only [unitaryMatrix, Sw, ← Matrix.mul_assoc, Matrix.mul_diagonal] at h
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Ne.symm hij,
    Equiv.swap_apply_def] at h
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at h
  · simpa [hij, Ne.symm hij] using h
  · intro x _ hx; simp [hx, Ne.symm hx]
  · simp
  · intro x _ hx
    by_cases hxj : x = j
    · subst hxj; simp [hij, hx]
    · simp [hx, hxj]
  · simp

lemma M1_trace (H : HaarLaw d) (X : Matrix (Fin d) (Fin d) ℂ) : (M1 H X).trace = X.trace := by
  haveI := H.probability
  unfold M1
  rw [← int_trace _ (integrable_of_cont H (M1_cont X))]
  have : ∀ V : SU d, (unitaryMatrix V * X * (unitaryMatrix V)ᴴ).trace = X.trace := fun V => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, unit_left, Matrix.one_mul]
  simp only [this, integral_const, probReal_univ, one_smul]

lemma M1_formula (H : HaarLaw d) (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    M1 H X i j = if i = j then X.trace / d else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ← M1_trace H X, Matrix.trace]
    simp only [Matrix.diag]
    rw [Finset.sum_congr rfl fun k _ => M1_diag H X k i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  · rw [if_neg hij, M1_offdiag H X i j hij]

end X7P21

namespace X7P21

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def ptr (M : Matrix (ι × κ) (ι × κ) ℂ) : Matrix κ κ ℂ := fun k k' => ∑ i, M (i, k) (i, k')

lemma ptr_kron_one_comm (A : Matrix ι ι ℂ) (N : Matrix (ι × κ) (ι × κ) ℂ) :
    ptr ((A ⊗ₖ (1 : Matrix κ κ ℂ)) * N) = ptr (N * (A ⊗ₖ (1 : Matrix κ κ ℂ))) := by
  ext k k'
  simp only [ptr, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma ptr_one_kron_mul (B : Matrix κ κ ℂ) (N : Matrix (ι × κ) (ι × κ) ℂ) :
    ptr (((1 : Matrix ι ι ℂ) ⊗ₖ B) * N) = B * ptr N := by
  ext k k'
  simp only [ptr, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type_right, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum]
  rw [Finset.sum_comm]

lemma ptr_mul_one_kron (B : Matrix κ κ ℂ) (N : Matrix (ι × κ) (ι × κ) ℂ) :
    ptr (N * ((1 : Matrix ι ι ℂ) ⊗ₖ B)) = ptr N * B := by
  ext k k'
  simp only [ptr, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type_right, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ptr_conj (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (hA : Aᴴ * A = 1) (M : Matrix (ι × κ) (ι × κ) ℂ) :
    ptr ((A ⊗ₖ B) * M * (A ⊗ₖ B)ᴴ) = B * ptr M * Bᴴ := by
  have h1 : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix κ κ ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have h2 : (A ⊗ₖ B)ᴴ = ((1 : Matrix ι ι ℂ) ⊗ₖ Bᴴ) * (Aᴴ ⊗ₖ (1 : Matrix κ κ ℂ)) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h2, h1]
  simp only [Matrix.mul_assoc]
  rw [ptr_kron_one_comm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_kronecker_mul, hA, Matrix.mul_one, Matrix.one_kronecker_one, Matrix.mul_one,
    ptr_one_kron_mul, ← Matrix.mul_assoc, ptr_mul_one_kron, Matrix.mul_assoc]

lemma ptr_trace (M : Matrix (ι × κ) (ι × κ) ℂ) : (ptr M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, ptr, Fintype.sum_prod_type]
  exact Finset.sum_comm

def ptrE (i : ι) : Matrix (ι × κ) κ ℂ := Matrix.of fun p k => if p.1 = i ∧ p.2 = k then 1 else 0

lemma ptr_psd (M : Matrix (ι × κ) (ι × κ) ℂ) (hM : M.PosSemidef) : (ptr M).PosSemidef := by
  have : ptr M = ∑ i : ι, (ptrE (κ := κ) i)ᴴ * M * ptrE (κ := κ) i := by
    ext k k'
    simp only [ptr, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, ptrE, Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel, apply_ite (starRingEnd ℂ), ite_mul]
  rw [this]
  exact Matrix.posSemidef_sum _ fun i _ => hM.conjTranspose_mul_mul_same _

end X7P21

namespace X7P21
open QAlgorithms.Papers.Independent.Claimed50.P21

lemma kron_cont {X : Type*} [TopologicalSpace X] {l m n p : Type*} {A : X → Matrix l m ℂ}
    {B : X → Matrix n p ℂ} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ⊗ₖ B x :=
  continuous_matrix fun i j => by
    simp only [Matrix.kroneckerMap_apply]
    exact (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

lemma bar_unit {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (h : Uᴴ * U = 1) :
    (U.map conj)ᴴ * U.map conj = 1 := by
  have e : (U.map conj)ᴴ = (Uᴴ).map conj := by ext i j; simp [Matrix.conjTranspose_apply]
  rw [e, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

lemma kron_unit {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, hB, Matrix.one_kronecker_one]

lemma unit_comm {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (h : Uᴴ * U = 1) :
    U * Uᴴ = 1 := mul_eq_one_comm.mp h

variable {d : ℕ}

lemma ubar_unit (V : SU d) : ((unitaryMatrix V).map conj)ᴴ * (unitaryMatrix V).map conj = 1 :=
  bar_unit _ (unit_left V)

lemma rep_unit (V W : SU d) : (representation V W)ᴴ * representation V W = 1 := by
  unfold representation
  exact kron_unit _ _ (kron_unit _ _ (unit_left V) (ubar_unit V)) (kron_unit _ _ (unit_left W) (ubar_unit W))

lemma cD_cont (X : Matrix (Four d) (Four d) ℂ) : Continuous (covariantDensity X) := by
  have hr : Continuous fun V : SU d => representation V 1 := by
    unfold representation
    exact kron_cont (kron_cont val_cont (val_cont.matrix_map (Complex.continuous_conj)))
      continuous_const
  unfold covariantDensity covarianceAction
  exact (hr.matrix_mul continuous_const).matrix_mul hr.matrix_conjTranspose

/-- integral of PSD-valued functions is PSD -/
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


abbrev ub (V : SU d) : Matrix (Wire d) (Wire d) ℂ := (unitaryMatrix V).map conj

lemma M1c (H : HaarLaw d) (hd : 0 < d) (Y : Matrix (Wire d) (Wire d) ℂ) (b b' : Wire d) :
    ∫ V, (ub V * Y * (ub V)ᴴ) b b' ∂H.law = if b = b' then Y.trace / d else 0 := by
  have e : ∀ V : SU d, (ub V * Y * (ub V)ᴴ) b b' =
      conj ((unitaryMatrix V * Y.map conj * (unitaryMatrix V)ᴴ) b b') := by
    intro V
    have : ub V * Y * (ub V)ᴴ = (unitaryMatrix V * Y.map conj * (unitaryMatrix V)ᴴ).map conj := by
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 1
      · congr 1; ext i j; simp
      all_goals try (ext i j; simp [Matrix.conjTranspose_apply])
    rw [this, Matrix.map_apply]
  simp_rw [e]
  rw [integral_conj, ← entry _ (integrable_of_cont H (M1_cont _))]
  have := M1_formula H hd (Y.map conj) b b'
  unfold M1 at this
  rw [this]
  have ht : (Y.map conj).trace = conj Y.trace := by simp [Matrix.trace, map_sum]
  split_ifs <;> simp [ht]

def slice {κ : Type*} (Y : Matrix (Wire d × κ) (Wire d × κ) ℂ) (k k' : κ) : Matrix (Wire d) (Wire d) ℂ :=
  Matrix.of fun β β' => Y (β, k) (β', k')

lemma slice_entry {κ : Type*} [Fintype κ] [DecidableEq κ] (B : Matrix (Wire d) (Wire d) ℂ)
    (Y : Matrix (Wire d × κ) (Wire d × κ) ℂ) (b b' : Wire d) (k k' : κ) :
    ((B ⊗ₖ (1 : Matrix κ κ ℂ)) * Y * (B ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) (b, k) (b', k') =
      (B * slice Y k k' * Bᴴ) b b' := by
  simp only [slice, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Matrix.of_apply]
  simp only [Complex.star_def, apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul]


abbrev TT (d : ℕ) := Equiv.prodAssoc (Wire d) (Wire d) (Wire d × Wire d)

lemma one_bar : ((1 : Matrix (Wire d) (Wire d) ℂ).map conj) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

lemma rep1 (V : SU d) : representation V 1 =
    (unitaryMatrix V ⊗ₖ ub V) ⊗ₖ (1 : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ) := by
  unfold representation
  have : unitaryMatrix (1 : SU d) = 1 := rfl
  rw [this, one_bar, Matrix.one_kronecker_one]

lemma cD_ptr (X : Matrix (Four d) (Four d) ℂ) (V : SU d) (b b' : Wire d) (k k' : Wire d × Wire d) :
    ∑ a, covariantDensity X V ((a, b), k) ((a, b'), k') =
      (ub V * slice (ptr (X.submatrix (TT d).symm (TT d).symm)) k k' * (ub V)ᴴ) b b' := by
  have h : ∑ a, covariantDensity X V ((a, b), k) ((a, b'), k') =
      ptr ((covariantDensity X V).submatrix (TT d).symm (TT d).symm) (b, k) (b', k') := rfl
  rw [h, covariantDensity, covarianceAction, rep1]
  rw [← Matrix.submatrix_mul_equiv _ _ _ (TT d).symm _, ← Matrix.submatrix_mul_equiv _ _ _ (TT d).symm _,
    ← Matrix.conjTranspose_submatrix, Matrix.kronecker_assoc', ptr_conj _ _ (unit_left V)]
  exact slice_entry _ _ _ _ _ _


lemma slice_trace (X : Matrix (Four d) (Four d) ℂ) (k k' : Wire d × Wire d) :
    (slice (ptr (X.submatrix (TT d).symm (TT d).symm)) k k').trace = ptr X k k' := by
  simp only [slice, ptr, Matrix.trace, Matrix.diag, Matrix.of_apply, Matrix.submatrix_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rfl

lemma Z_inv (X : Matrix (Four d) (Four d) ℂ) (hc : SeedCommutes X) (V : SU d) :
    ub V * ptr (ptr X) * (ub V)ᴴ = ptr (ptr X) := by
  have hR := rep_unit V V
  have hX : X = representation V V * X * (representation V V)ᴴ := by
    rw [← hc V, Matrix.mul_assoc, unit_comm _ hR, Matrix.mul_one]
  conv_rhs => rw [hX]
  unfold representation
  rw [ptr_conj _ _ (kron_unit _ _ (unit_left V) (ubar_unit V)), ptr_conj _ _ (unit_left V)]

theorem main (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d)
    (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef) (hc : SeedCommutes X) :
    IsDeterministicTwoComb (∫ V, covariantDensity X V ∂H.law) ↔ X.trace = (d : ℂ)^2 := by
  haveI := H.probability
  have hd0 : 0 < d := by omega
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hint : Integrable (covariantDensity X) H.law := integrable_of_cont H (cD_cont X)
  have hint2 : ∀ i j, Integrable (fun V => covariantDensity X V i j) H.law :=
    fun i j => integrable_of_cont H ((cD_cont X).matrix_elem i j)
  set I := ∫ V, covariantDensity X V ∂H.law with hI
  have htr : I.trace = X.trace := by
    rw [hI, ← int_trace _ hint]
    have : ∀ V : SU d, (covariantDensity X V).trace = X.trace := fun V => by
      rw [covariantDensity, covarianceAction, Matrix.trace_mul_comm, ← Matrix.mul_assoc, rep_unit,
        Matrix.one_mul]
    simp only [this, integral_const, probReal_univ, one_smul]
  have hsum1 : ∀ (b b' : Wire d) (k k' : Wire d × Wire d),
      ∑ a, I ((a, b), k) ((a, b'), k') = if b = b' then ptr X k k' / d else 0 := by
    intro b b' k k'
    simp only [hI, entry _ hint]
    rw [← integral_finset_sum _ (fun a _ => hint2 _ _)]
    simp_rw [cD_ptr]
    rw [M1c H hd0, slice_trace]
  constructor
  · rintro ⟨_, Rone, _, h1, h2⟩
    rw [← htr]
    have e1 : I.trace = ∑ b, ∑ c, ∑ e, ∑ a, I ((a, b), (c, e)) ((a, b), (c, e)) := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
    rw [e1]
    simp only [h1, if_true, one_mul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_comm]
    simp only [h2, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  · intro ht
    refine ⟨int_psd _ hint (fun V => hX.mul_mul_conjTranspose_same _),
      (((d : ℝ)⁻¹ : ℝ) : ℂ) • ptr X, (ptr_psd X hX).smul (Complex.zero_le_real.mpr (by positivity)), ?_, ?_⟩
    · intro b c e b' c' e'
      rw [hsum1 b b' (c, e) (c', e')]
      split_ifs <;> simp [Matrix.smul_apply] <;> field_simp
    · intro e e'
      have hZ : ptr (ptr X) e e' = if e = e' then (ptr (ptr X)).trace / d else 0 := by
        rw [← M1c H hd0]
        have : ∀ V : SU d, (ub V * ptr (ptr X) * (ub V)ᴴ) e e' = ptr (ptr X) e e' := fun V => by
          rw [Z_inv X hc V]
        simp only [this, integral_const, probReal_univ, one_smul]
      have : ∑ c, ((((d : ℝ)⁻¹ : ℝ) : ℂ) • ptr X) (c, e) (c, e') = (d : ℂ)⁻¹ * ptr (ptr X) e e' := by
        simp [Matrix.smul_apply, ptr, Finset.mul_sum]
      rw [this, hZ, ptr_trace, ptr_trace, ht]
      split_ifs <;> field_simp <;> simp

end X7P21



-- ===== p21s/S1 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21 X7TW

variable {d : ℕ}

lemma eP_eq : entangledProjector d = Pm d := by
  ext p q
  simp only [entangledProjector, pureDensity, Pm, Phi, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Matrix.vec, Matrix.transpose_apply, Matrix.one_apply]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2, eq_comm]

lemma Pm_ct : (Pm d)ᴴ = Pm d := by
  rw [Pm, Matrix.conjTranspose_smul, Phi_ct]; simp

lemma Pm_sq (hd : 0 < d) : Pm d * Pm d = Pm d := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Pm, Matrix.smul_mul, Matrix.mul_smul, Phi_sq, smul_smul, smul_smul]
  congr 1; field_simp

lemma Qm_ct : (Qm d)ᴴ = Qm d := by
  rw [Qm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Pm_ct]

lemma Qm_sq (hd : 0 < d) : Qm d * Qm d = Qm d := by
  rw [Qm, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Pm_sq hd]; simp

lemma psd_of_proj {n : Type*} [Fintype n] (M : Matrix n n ℂ) (h1 : Mᴴ = M) (h2 : M * M = M) :
    M.PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self M
  rwa [h1, h2] at this

lemma Pm_psd (hd : 0 < d) : (Pm d).PosSemidef := psd_of_proj _ Pm_ct (Pm_sq hd)
lemma Qm_psd (hd : 0 < d) : (Qm d).PosSemidef := psd_of_proj _ Qm_ct (Qm_sq hd)

lemma lamF_eq : lambdaF d = (((d : ℂ)^2 * ((d : ℂ)^2 - 1))⁻¹) •
    (Qm d ⊗ₖ Qm d + ((d : ℂ)^2 - 1) • (Pm d ⊗ₖ Pm d)) := by
  rw [lambdaF, eP_eq]
  congr 1
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [Qm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul]
  rw [Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h1 : i1 = j1 <;> by_cases h2 : i2 = j2 <;> simp [h1, h2] <;> ring

lemma nn_smul {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) (r : ℝ) (hr : 0 ≤ r) :
    ((r : ℂ) • M).PosSemidef :=
  hM.smul (Complex.zero_le_real.mpr hr)

lemma cst : (((d : ℂ)^2 * ((d : ℂ)^2 - 1))⁻¹) = Complex.ofReal (((d : ℝ)^2 * ((d : ℝ)^2 - 1))⁻¹) := by
  push_cast; rfl

lemma cst_pos (hd : 2 ≤ d) : 0 ≤ (((d : ℝ)^2 * ((d : ℝ)^2 - 1))⁻¹ : ℝ) := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : 0 ≤ (d : ℝ)^2 - 1 := by nlinarith
  positivity

theorem lamF_psd (hd : 2 ≤ d) : (lambdaF d).PosSemidef := by
  have hd0 : 0 < d := by omega
  rw [lamF_eq, cst]
  refine nn_smul ?_ _ (cst_pos hd)
  refine ((Qm_psd hd0).kronecker (Qm_psd hd0)).add ?_
  have : ((d : ℂ)^2 - 1) = Complex.ofReal ((d : ℝ)^2 - 1) := by push_cast; rfl
  rw [this]
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact nn_smul ((Pm_psd hd0).kronecker (Pm_psd hd0)) _ (by nlinarith)

lemma mid_entry (i j : Four d) : middleProjector d i j =
    (if i.1.1 = j.1.1 then 1 else 0) * Pm d (i.1.2, i.2.1) (j.1.2, j.2.1) * (if i.2.2 = j.2.2 then 1 else 0) := by
  rw [middleProjector, eP_eq]

lemma mid_ct : (middleProjector d)ᴴ = middleProjector d := by
  ext i j
  rw [Matrix.conjTranspose_apply, mid_entry, mid_entry]
  have := congrFun (congrFun (Pm_ct (d := d)) (i.1.2, i.2.1)) (j.1.2, j.2.1)
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]
  by_cases h1 : i.1.1 = j.1.1 <;> by_cases h2 : i.2.2 = j.2.2 <;> simp [h1, h2, eq_comm]

lemma mid_sq (hd : 0 < d) : middleProjector d * middleProjector d = middleProjector d := by
  ext i j
  have hP := congrFun (congrFun (Pm_sq hd) (i.1.2, i.2.1)) (j.1.2, j.2.1)
  rw [Matrix.mul_apply] at hP
  rw [Matrix.mul_apply, mid_entry, ← hP]
  simp only [mid_entry, Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  by_cases h1 : i.1.1 = j.1.1 <;> by_cases h2 : i.2.2 = j.2.2 <;>
    simp [h1, h2, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

theorem lamG_psd (hd : 2 ≤ d) : (lambdaG d).PosSemidef := by
  have hd0 : 0 < d := by omega
  rw [lambdaG, cst]
  refine nn_smul ?_ _ (cst_pos hd)
  refine Matrix.PosSemidef.add ?_ (psd_of_proj _ mid_ct (mid_sq hd0))
  have : ((1 - 2 / (d : ℂ)^2) : ℂ) = Complex.ofReal (1 - 2 / (d : ℝ)^2) := by push_cast; rfl
  rw [this]
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h4 : (4 : ℝ) ≤ (d : ℝ)^2 := by nlinarith
  refine nn_smul Matrix.PosSemidef.one _ ?_
  rw [sub_nonneg, div_le_one (by positivity)]; linarith

theorem bell (hd : 2 ≤ d) : lambdaG d = gainBellContraction (lambdaF d) := by
  have hd0 : 0 < d := by omega
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  ext i j
  obtain ⟨⟨i3, i2⟩, ⟨i1, i0⟩⟩ := i
  obtain ⟨⟨j3, j2⟩, ⟨j1, j0⟩⟩ := j
  simp only [gainBellContraction, lambdaG, lambdaF, eP_eq, mid_entry, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.kronecker_apply, Matrix.one_apply, Pm, Phi, Matrix.of_apply, smul_eq_mul,
    Prod.mk.injEq]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [ite_and, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  split_ifs <;> subst_vars <;> simp_all <;> field_simp <;> ring

end X7PS

-- ===== p21s/S2 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

variable {d : ℕ}

lemma umul (V U : SU d) : unitaryMatrix (X7P21.sinv V * U) = (unitaryMatrix V)ᴴ * unitaryMatrix U := rfl

lemma qf_def (v : Four d → ℂ) (M : Matrix (Four d) (Four d) ℂ) :
    Measurements.quadraticFunctional v M = star v ⬝ᵥ (M *ᵥ v) := rfl

lemma qf_conj (v : Four d → ℂ) (A M : Matrix (Four d) (Four d) ℂ) :
    Measurements.quadraticFunctional v (A * M * Aᴴ) = Measurements.quadraticFunctional (Aᴴ *ᵥ v) M := by
  rw [qf_def, qf_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

lemma fv_rep (V U : SU d) :
    (representation V 1)ᴴ *ᵥ fidelityVector U = fidelityVector (X7P21.sinv V * U) := by
  ext ⟨⟨k3, k2⟩, ⟨k1, k0⟩⟩
  rw [X7P21.rep1]
  simp only [fidelityVector, umul]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, fidelityVector, Matrix.mul_apply, Matrix.map_apply,
    Prod.mk.injEq]
  simp only [star_mul', Complex.star_def, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_and, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sum, map_mul,
    Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single k1 (fun x _ hx => by simp [hx]) (by simp)]
  simp only [if_true, Finset.sum_ite_eq', Finset.mem_univ]
  ring

def gF (X : Matrix (Four d) (Four d) ℂ) (W : SU d) : ℝ :=
  (Measurements.quadraticFunctional (fidelityVector W) X).re / (d : ℝ)^2

lemma fk_eq (X : Matrix (Four d) (Four d) ℂ) (U V : SU d) :
    fidelityKernel (covariantDensity X V) U = gF X (X7P21.sinv V * U) := by
  rw [fidelityKernel, gF, covariantDensity, covarianceAction, qf_conj, fv_rep]

end X7PS

-- ===== p21s/S3 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

variable {d : ℕ}

/-- contracted link: Σ_a linkedChoi R U (a,e) (a,e') -/
def Lk (R : Matrix (Four d) (Four d) ℂ) (W : Matrix (Wire d) (Wire d) ℂ) (e e' : Wire d) : ℂ :=
  ∑ c, ∑ c', ∑ b, ∑ b', W b c * (∑ a, R ((a, b), (c, e)) ((a, b'), (c', e'))) * conj (W b' c')

lemma reord (f : Wire d → Wire d → Wire d → Wire d → Wire d → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ b', ∑ c', f a b c b' c' = ∑ c, ∑ c', ∑ b, ∑ b', ∑ a, f a b c b' c' := by
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; arg 2; ext c; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; arg 2; ext c; arg 2; ext b'; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]

lemma oD_eq (R : Matrix (Four d) (Four d) ℂ) (U : SU d) (ρ : Matrix (Wire d) (Wire d) ℂ) :
    outcomeDensity R U ρ = (∑ e, ∑ e', Lk R (unitaryMatrix U) e e' * ρ e e').re := by
  rw [outcomeDensity]
  congr 1
  simp only [insertedOutput, Matrix.trace, Matrix.diag]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  simp only [linkedChoi, Lk, Finset.mul_sum, Finset.sum_mul]
  exact reord _

lemma quad_entry (A S : Matrix (Wire d) (Wire d) ℂ) (c c' : Wire d) :
    ∑ b, ∑ b', A b c * S b b' * conj (A b' c') = (Aᵀ * S * A.map conj) c c' := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma Lk_cov (X : Matrix (Four d) (Four d) ℂ) (V U : SU d) (e e' : Wire d) :
    Lk (covariantDensity X V) (unitaryMatrix U) e e' = Lk X (unitaryMatrix (X7P21.sinv V * U)) e e' := by
  unfold Lk
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  simp_rw [X7P21.cD_ptr]
  have hs : ∀ b b', (∑ a, X ((a, b), (c, e)) ((a, b'), (c', e'))) =
      X7P21.slice (X7P21.ptr (X.submatrix (X7P21.TT d).symm (X7P21.TT d).symm)) (c, e) (c', e') b b' :=
    fun _ _ => rfl
  simp_rw [hs]
  rw [quad_entry, quad_entry, umul]
  have h1 : ((unitaryMatrix V)ᴴ * unitaryMatrix U)ᵀ = (unitaryMatrix U)ᵀ * X7P21.ub V := by
    rw [Matrix.transpose_mul]; rfl
  have h2 : ((unitaryMatrix V)ᴴ * unitaryMatrix U).map conj = (X7P21.ub V)ᴴ * (unitaryMatrix U).map conj := by
    rw [Matrix.map_mul]; congr 1
  rw [h1, h2]
  simp only [Matrix.mul_assoc]

end X7PS

-- ===== p21s/S4 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

variable {d : ℕ}

def Yc (X : Matrix (Four d) (Four d) ℂ) : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ :=
  fun p q => ∑ a, ∑ e, X ((a, p.1), (p.2, e)) ((a, q.1), (q.2, e))

def sg (d : ℕ) : Four d ≃ (Wire d × Wire d) × (Wire d × Wire d) :=
  ⟨fun p => ((p.1.1, p.2.2), (p.1.2, p.2.1)), fun q => ((q.1.1, q.2.1), (q.2.2, q.1.2)),
    fun _ => rfl, fun _ => rfl⟩

lemma Yc_ptr (X : Matrix (Four d) (Four d) ℂ) :
    Yc X = X7P21.ptr (X.submatrix (sg d).symm (sg d).symm) := by
  ext p q
  simp only [Yc, X7P21.ptr, Fintype.sum_prod_type]
  rfl

lemma Rt (V : SU d) : (representation V V).submatrix (sg d).symm (sg d).symm =
    (unitaryMatrix V ⊗ₖ X7P21.ub V) ⊗ₖ (X7P21.ub V ⊗ₖ unitaryMatrix V) := by
  ext ⟨⟨a, e⟩, ⟨b, c⟩⟩ ⟨⟨a', e'⟩, ⟨b', c'⟩⟩
  simp only [representation, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, sg, Equiv.coe_fn_symm_mk,
    X7P21.ub]
  ring

lemma Y_comm (X : Matrix (Four d) (Four d) ℂ) (hc : SeedCommutes X) (V : SU d) :
    Yc X * (X7P21.ub V ⊗ₖ unitaryMatrix V) = (X7P21.ub V ⊗ₖ unitaryMatrix V) * Yc X := by
  set A := unitaryMatrix V ⊗ₖ X7P21.ub V
  set B := X7P21.ub V ⊗ₖ unitaryMatrix V
  have hA : Aᴴ * A = 1 := X7P21.kron_unit _ _ (X7P21.unit_left V) (X7P21.ubar_unit V)
  have hB : Bᴴ * B = 1 := X7P21.kron_unit _ _ (X7P21.ubar_unit V) (X7P21.unit_left V)
  have hR : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := X7P21.kron_unit _ _ hA hB
  set Xt := X.submatrix (sg d).symm (sg d).symm
  have hXR : Xt * (A ⊗ₖ B) = (A ⊗ₖ B) * Xt := by
    rw [← Rt, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hc V]
  have hX : Xt = (A ⊗ₖ B) * Xt * (A ⊗ₖ B)ᴴ := by
    rw [← hXR, Matrix.mul_assoc, X7P21.unit_comm _ hR, Matrix.mul_one]
  have hY0 : X7P21.ptr Xt = B * X7P21.ptr Xt * Bᴴ := by
    conv_lhs => rw [hX]
    rw [X7P21.ptr_conj _ _ hA]
  have hY : Yc X = B * Yc X * Bᴴ := by
    rw [Yc_ptr]; exact hY0
  conv_lhs => rw [hY]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hB, Matrix.mul_one]

theorem Y_form (hd : 2 ≤ d) (X : Matrix (Four d) (Four d) ℂ) (hc : SeedCommutes X) :
    ∃ x y : ℂ, ∀ b c b' c' : Wire d, Yc X (b, c) (b', c') =
      x * (if b = b' ∧ c = c' then 1 else 0) + y * (if b = c ∧ b' = c' then 1 else 0) := by
  set N := (Yc X).submatrix Prod.swap Prod.swap
  have hN : ∀ V ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
      N * (V ⊗ₖ V.map conj) = (V ⊗ₖ V.map conj) * N := by
    intro V hV
    have h := Y_comm X hc ⟨V, hV⟩
    have hs : (V ⊗ₖ V.map conj) = (X7P21.ub ⟨V, hV⟩ ⊗ₖ unitaryMatrix ⟨V, hV⟩).submatrix Prod.swap Prod.swap := by
      ext p q; simp [X7P21.ub, unitaryMatrix, mul_comm]
    rw [hs]
    have e : ∀ M M' : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ,
        M.submatrix Prod.swap Prod.swap * M'.submatrix Prod.swap Prod.swap = (M * M').submatrix Prod.swap Prod.swap :=
      fun M M' => Matrix.submatrix_mul_equiv M M' (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    rw [e, e, h]
  obtain ⟨x, y, hxy⟩ := X7TW.commutant hd N hN
  refine ⟨x, y, fun b c b' c' => ?_⟩
  have := congrFun (congrFun hxy (c, b)) (c', b')
  simp only [N, Matrix.submatrix_apply, Prod.swap_prod_mk, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, X7TW.Phi, Matrix.of_apply, smul_eq_mul, Prod.mk.injEq] at this
  rw [this]
  by_cases h1 : b = b' <;> by_cases h2 : c = c' <;> by_cases h3 : b = c <;> by_cases h4 : b' = c' <;>
    simp [h1, h2, h3, h4, eq_comm]

lemma Lk_diag (X : Matrix (Four d) (Four d) ℂ) (W : Matrix (Wire d) (Wire d) ℂ) :
    ∑ e, Lk X W e e = ∑ c, ∑ c', ∑ b, ∑ b', W b c * Yc X (b, c) (b', c') * conj (W b' c') := by
  unfold Lk Yc
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b' _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  exact Finset.sum_comm

end X7PS

-- ===== p21s/S5 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

variable {d : ℕ}

lemma hinv (H : HaarLaw d) : ∀ (W : SU d) (f : SU d → ℂ), Continuous f →
    ∫ V, f (W * V) ∂H.law = ∫ V, f V ∂H.law :=
  fun W f hf => X7P21.int_left H f hf W

def nn (W : SU d) : ℝ := Complex.normSq (unitaryMatrix W).trace

lemma nn_C (W : SU d) : ((nn W : ℝ) : ℂ) = ∑ a, ∑ b, unitaryMatrix W a a * conj (unitaryMatrix W b b) := by
  rw [nn, ← Complex.mul_conj, Matrix.trace, map_sum, Finset.sum_mul]
  simp only [Matrix.diag, Finset.mul_sum]

lemma nn_cont : Continuous (nn (d := d)) := by
  unfold nn
  exact Complex.continuous_normSq.comp (continuous_finset_sum _ fun i _ =>
    (X7P21.val_cont.matrix_elem i i))

lemma int_nn (H : HaarLaw d) (hd : 0 < d) : ∫ W, nn W ∂H.law = 1 := by
  haveI := H.probability
  have hC : ((∫ W, nn W ∂H.law : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    simp_rw [nn_C]
    have hi : ∀ a b : Wire d, Integrable (fun W : SU d => unitaryMatrix W a a * conj (unitaryMatrix W b b)) H.law :=
      fun a b => X7P21.integrable_of_cont H ((X7P21.val_cont.matrix_elem a a).mul
        (Complex.continuous_conj.comp (X7P21.val_cont.matrix_elem b b)))
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hi a b]
    simp_rw [integral_finset_sum _ fun b _ => hi _ b]
    have e : ∀ a b : Wire d, ∫ W, unitaryMatrix W a a * conj (unitaryMatrix W b b) ∂H.law =
        if a = b then (d : ℂ)⁻¹ else 0 := by
      intro a b
      have h1 : ∀ W : SU d, unitaryMatrix W a a * conj (unitaryMatrix W b b) =
          (unitaryMatrix W * Matrix.single a b (1 : ℂ) * (unitaryMatrix W)ᴴ) a b := by
        intro W
        simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, mul_ite,
          mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          Finset.sum_ite_irrel, Finset.sum_const_zero]
        simp [Complex.star_def]
      simp_rw [h1]
      rw [← X7P21.entry _ (X7P21.integrable_of_cont H (X7P21.M1_cont _))]
      have := X7P21.M1_formula H hd (Matrix.single a b (1 : ℂ)) a b
      rw [X7P21.M1] at this
      rw [this]
      by_cases h : a = b
      · subst h; simp [Matrix.trace_single_eq_same]
      · simp [h]
    simp_rw [e]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  exact_mod_cast hC

lemma Pm_sym (p q : Wire d × Wire d) : X7TW.Pm d p q = X7TW.Pm d q p := by
  simp only [X7TW.Pm, X7TW.Phi, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, and_comm]

lemma Qm_sym (p q : Wire d × Wire d) : X7TW.Qm d p q = X7TW.Qm d q p := by
  simp only [X7TW.Qm, Matrix.sub_apply, Pm_sym p q, Matrix.one_apply, eq_comm]

lemma Pm_sw (a b c e : Wire d) : X7TW.Pm d (a, b) (c, e) = X7TW.Pm d (b, a) (e, c) := by
  simp only [X7TW.Pm, X7TW.Phi, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, eq_comm]

lemma Qm_sw (a b c e : Wire d) : X7TW.Qm d (a, b) (c, e) = X7TW.Qm d (b, a) (e, c) := by
  simp only [X7TW.Qm, Matrix.sub_apply, Pm_sw a b c e, Matrix.one_apply, Prod.mk.injEq, and_comm]

lemma Pm_tr (hd : 0 < d) : (X7TW.Pm d).trace = 1 := by
  rw [X7TW.Pm, Matrix.trace_smul, X7TW.Phi_trace, smul_eq_mul]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

lemma Qm_tr (hd : 0 < d) : (X7TW.Qm d).trace = (d : ℂ)^2 - 1 := by
  rw [X7TW.Qm, Matrix.trace_sub, Pm_tr hd, Matrix.trace_one]
  simp [Fintype.card_prod, sq]

lemma sq_sum_P (hd : 0 < d) : ∑ p, ∑ q, X7TW.Pm d p q * X7TW.Pm d p q = 1 := by
  have h : (X7TW.Pm d * X7TW.Pm d).trace = ∑ p, ∑ q, X7TW.Pm d p q * X7TW.Pm d p q := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Pm_sym q p]
  rw [← h, Pm_sq hd, Pm_tr hd]

lemma sq_sum_Q (hd : 0 < d) : ∑ p, ∑ q, X7TW.Qm d p q * X7TW.Qm d p q = (d : ℂ)^2 - 1 := by
  have h : (X7TW.Qm d * X7TW.Qm d).trace = ∑ p, ∑ q, X7TW.Qm d p q * X7TW.Qm d p q := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Qm_sym q p]
  rw [← h, Qm_sq hd, Qm_tr hd]

lemma K_cont : Continuous fun W : SU d => X7TW.K (unitaryMatrix W) :=
  X7TW.K_cont (d := d)

lemma Kint (H : HaarLaw d) (a b c e : Wire d × Wire d) :
    Integrable (fun W : SU d => X7TW.K (unitaryMatrix W) a b * conj (X7TW.K (unitaryMatrix W) c e)) H.law :=
  X7P21.integrable_of_cont H ((K_cont.matrix_elem a b).mul (Complex.continuous_conj.comp (K_cont.matrix_elem c e)))

lemma wgH (H : HaarLaw d) (hd : 2 ≤ d) (a b c e : Wire d × Wire d) :
    ∫ W, X7TW.K (unitaryMatrix W) a b * conj (X7TW.K (unitaryMatrix W) c e) ∂H.law =
      X7TW.Pm d a c * X7TW.Pm d b e + X7TW.Qm d a c * X7TW.Qm d b e / ((d : ℂ) ^ 2 - 1) := by
  haveI := H.probability
  exact X7TW.wg H.law (hinv H) hd a b c e

lemma nn_K (W : SU d) : ((nn W : ℝ) : ℂ) = ∑ p, X7TW.K (unitaryMatrix W) p p := by
  rw [nn_C, Fintype.sum_prod_type]
  simp [X7TW.K, Matrix.kroneckerMap_apply]

lemma int_nn2 (H : HaarLaw d) (hd : 2 ≤ d) : ∫ W, nn W ^ 2 ∂H.law = 2 := by
  have hd0 : 0 < d := by omega
  have hC : ((∫ W, nn W ^ 2 ∂H.law : ℝ) : ℂ) = 2 := by
    rw [← integral_complex_ofReal]
    have e : ∀ W : SU d, (((nn W ^ 2 : ℝ)) : ℂ) =
        ∑ p, ∑ q, X7TW.K (unitaryMatrix W) p p * conj (X7TW.K (unitaryMatrix W) q q) := by
      intro W
      have h1 := nn_K W
      have h2 : conj ((nn W : ℝ) : ℂ) = ((nn W : ℝ) : ℂ) := Complex.conj_ofReal _
      rw [Complex.ofReal_pow, sq]
      conv_lhs => arg 2; rw [← h2]
      rw [h1, map_sum, Finset.sum_mul_sum]
    simp_rw [e]
    rw [integral_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ => Kint H _ _ _ _]
    simp_rw [integral_finset_sum _ fun q _ => Kint H _ _ _ _, wgH H hd]
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib, Finset.sum_add_distrib, sq_sum_P hd0]
    simp_rw [← Finset.sum_div]
    rw [sq_sum_Q hd0]
    have : (d : ℂ)^2 - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      intro h
      have h' : ((d : ℝ)^2 - 1 : ℝ) = 0 := by exact_mod_cast h
      nlinarith
    field_simp; ring
  exact_mod_cast hC

end X7PS

-- ===== p21s/S6 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

variable {d : ℕ}

abbrev pp (i : Four d) : Wire d × Wire d := (i.1.1, i.1.2)
abbrev qq (i : Four d) : Wire d × Wire d := (i.2.2, i.2.1)

lemma qf_fv (X : Matrix (Four d) (Four d) ℂ) (W : SU d) :
    Measurements.quadraticFunctional (fidelityVector W) X =
      ∑ i, ∑ j, X i j * (X7TW.K (unitaryMatrix W) (pp j) (qq j) * conj (X7TW.K (unitaryMatrix W) (pp i) (qq i))) := by
  rw [qf_def]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [fidelityVector, X7TW.K, Matrix.kroneckerMap_apply, Matrix.map_apply, Complex.star_def]
  ring

lemma lamF_entry (j i : Four d) : lambdaF d j i = (((d : ℂ)^2 * ((d : ℂ)^2 - 1))⁻¹) *
    (X7TW.Qm d (pp j) (pp i) * X7TW.Qm d (qq j) (qq i) +
      ((d : ℂ)^2 - 1) * (X7TW.Pm d (pp j) (pp i) * X7TW.Pm d (qq j) (qq i))) := by
  rw [lamF_eq]
  obtain ⟨⟨j3, j2⟩, ⟨j1, j0⟩⟩ := j
  obtain ⟨⟨i3, i2⟩, ⟨i1, i0⟩⟩ := i
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, smul_eq_mul, pp, qq]
  rw [Qm_sw j1 j0 i1 i0, Pm_sw j1 j0 i1 i0]

lemma dsq_ne (hd : 2 ≤ d) : (d : ℂ)^2 - 1 ≠ 0 := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  intro h
  have h' : ((d : ℝ)^2 - 1 : ℝ) = 0 := by exact_mod_cast h
  nlinarith

lemma qf_int (H : HaarLaw d) (X : Matrix (Four d) (Four d) ℂ) :
    Integrable (fun W : SU d => Measurements.quadraticFunctional (fidelityVector W) X) H.law := by
  simp_rw [qf_fv]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (Kint H _ _ _ _).const_mul _

lemma int_qf (H : HaarLaw d) (hd : 2 ≤ d) (X : Matrix (Four d) (Four d) ℂ) :
    ∫ W, Measurements.quadraticFunctional (fidelityVector W) X ∂H.law = (d : ℂ)^2 * (lambdaF d * X).trace := by
  have hd0 : 0 < d := by omega
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  simp_rw [qf_fv]
  rw [integral_finset_sum (s := Finset.univ) (f := fun i (W : SU d) => ∑ j, X i j *
      (X7TW.K (unitaryMatrix W) (pp j) (qq j) * conj (X7TW.K (unitaryMatrix W) (pp i) (qq i))))
    fun i _ => integrable_finset_sum _ fun j _ => (Kint H _ _ _ _).const_mul _]
  have e : ∀ i : Four d, ∫ W, (∑ j, X i j *
      (X7TW.K (unitaryMatrix W) (pp j) (qq j) * conj (X7TW.K (unitaryMatrix W) (pp i) (qq i)))) ∂H.law =
      ∑ j, X i j * (X7TW.Pm d (pp j) (pp i) * X7TW.Pm d (qq j) (qq i) +
        X7TW.Qm d (pp j) (pp i) * X7TW.Qm d (qq j) (qq i) / ((d : ℂ) ^ 2 - 1)) := by
    intro i
    rw [integral_finset_sum (s := Finset.univ) (f := fun j (W : SU d) => X i j *
      (X7TW.K (unitaryMatrix W) (pp j) (qq j) * conj (X7TW.K (unitaryMatrix W) (pp i) (qq i))))
      fun j _ => (Kint H _ _ _ _).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, wgH H hd]
  simp only [e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [lamF_entry]
  have := dsq_ne hd
  field_simp
  ring

lemma int_gF (H : HaarLaw d) (hd : 2 ≤ d) (X : Matrix (Four d) (Four d) ℂ) :
    ∫ W, gF X W ∂H.law = ((lambdaF d * X).trace).re := by
  have hd0 : 0 < d := by omega
  unfold gF
  have hre := integral_re (qf_int H X)
  simp only [RCLike.re_to_complex] at hre
  rw [integral_div, hre, int_qf H hd]
  have : ((d : ℂ)^2 * (lambdaF d * X).trace).re = (d : ℝ)^2 * ((lambdaF d * X).trace).re := by
    rw [show ((d : ℂ)^2) = (((d : ℝ)^2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  rw [this]
  have : (d : ℝ)^2 ≠ 0 := by positivity
  field_simp

lemma gF_cont (X : Matrix (Four d) (Four d) ℂ) : Continuous (gF X) := by
  unfold gF
  simp_rw [qf_fv]
  refine Continuous.div_const (Complex.continuous_re.comp ?_) _
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_const.mul ((K_cont.matrix_elem _ _).mul (Complex.continuous_conj.comp (K_cont.matrix_elem _ _)))

lemma sinv_cont : Continuous (X7P21.sinv (d := d)) :=
  Continuous.subtype_mk X7P21.val_cont.matrix_conjTranspose _

lemma pair_cont : Continuous fun t : SU d × SU d => X7P21.sinv t.2 * t.1 :=
  (sinv_cont.comp continuous_snd).mul continuous_fst

lemma red (H : HaarLaw d) (g : SU d → ℝ) (hg : Continuous g) :
    ∫ t, g (X7P21.sinv t.2 * t.1) ∂(H.law.prod H.law) = ∫ W, g W ∂H.law := by
  haveI := H.probability
  have hc : Continuous fun t : SU d × SU d => g (X7P21.sinv t.2 * t.1) := hg.comp pair_cont
  rw [integral_prod_symm _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have : ∀ V : SU d, ∫ U, g (X7P21.sinv V * U) ∂H.law = ∫ W, g W ∂H.law :=
    fun V => X7P21.int_left H g hg (X7P21.sinv V)
  simp only [this, integral_const, probReal_univ, one_smul]

theorem score (H : HaarLaw d) (hd : 2 ≤ d) (X : Matrix (Four d) (Four d) ℂ) :
    channelScore H (covariantDensity X) = ((lambdaF d * X).trace).re := by
  rw [channelScore]
  simp_rw [fk_eq]
  rw [red H _ (gF_cont X), int_gF H hd]

end X7PS

-- ===== p21s/S7 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

variable {d : ℕ}

def YForm (X : Matrix (Four d) (Four d) ℂ) (x y : ℂ) : Prop :=
  ∀ b c b' c' : Wire d, Yc X (b, c) (b', c') =
      x * (if b = b' ∧ c = c' then 1 else 0) + y * (if b = c ∧ b' = c' then 1 else 0)

lemma sum_abs (W : SU d) : ∑ c, ∑ b, unitaryMatrix W b c * conj (unitaryMatrix W b c) = d := by
  have h := congrArg Matrix.trace (X7P21.unit_left W)
  rw [Matrix.trace_one, Fintype.card_fin] at h
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma diag_val (X : Matrix (Four d) (Four d) ℂ) (x y : ℂ) (hxy : YForm X x y) (W : SU d) :
    ∑ e, Lk X (unitaryMatrix W) e e = x * d + y * nn W := by
  rw [YForm] at hxy
  rw [Lk_diag, nn_C, ← sum_abs W]
  simp only [hxy, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

lemma oD_cD (X : Matrix (Four d) (Four d) ℂ) (x y : ℂ) (hxy : YForm X x y) (U V : SU d) :
    outcomeDensity (covariantDensity X V) U (((d : ℂ)⁻¹) • 1) =
      ((d : ℂ)⁻¹ * (x * d + y * nn (X7P21.sinv V * U))).re := by
  rw [oD_eq]
  simp_rw [Lk_cov]
  rw [← diag_val X x y hxy]
  congr 1
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

def gK (x y : ℂ) (W : SU d) : ℝ := ((d : ℂ)⁻¹ * (x * d + y * nn W)).re * nn W / (d : ℝ)^2

lemma gk_eq (X : Matrix (Four d) (Four d) ℂ) (x y : ℂ) (hxy : YForm X x y) (U V : SU d) :
    gainKernel (covariantDensity X V) U V = gK x y (X7P21.sinv V * U) := by
  rw [gainKernel, oD_cD X x y hxy, gK]
  rfl

lemma gK_eq (hd : 0 < d) (x y : ℂ) (W : SU d) :
    gK x y W = (x.re / (d : ℝ)^2) * nn W + (y.re / (d : ℝ)^3) * nn W ^ 2 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : (d : ℂ)⁻¹ * (x * d + y * (nn W : ℂ)) = x + y * ((nn W / d : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [gK, e, Complex.add_re, Complex.re_mul_ofReal]
  field_simp

lemma gK_cont (hd : 0 < d) (x y : ℂ) : Continuous (gK (d := d) x y) := by
  have : gK (d := d) x y = fun W => (x.re / (d : ℝ)^2) * nn W + (y.re / (d : ℝ)^3) * nn W ^ 2 :=
    funext (gK_eq hd x y)
  rw [this]
  exact (continuous_const.mul nn_cont).add (continuous_const.mul (nn_cont.pow 2))

lemma int_gK (H : HaarLaw d) (hd : 2 ≤ d) (x y : ℂ) :
    ∫ W, gK x y W ∂H.law = x.re / (d : ℝ)^2 + 2 * y.re / (d : ℝ)^3 := by
  have hd0 : 0 < d := by omega
  simp_rw [gK_eq hd0]
  have i1 : Integrable (fun W : SU d => x.re / (d : ℝ)^2 * nn W) H.law :=
    (X7P21.integrable_of_cont H nn_cont).const_mul _
  have i2 : Integrable (fun W : SU d => y.re / (d : ℝ)^3 * nn W ^ 2) H.law :=
    (X7P21.integrable_of_cont H (nn_cont.pow 2)).const_mul _
  rw [integral_add i1 i2,
    integral_const_mul, integral_const_mul, int_nn H hd0, int_nn2 H hd]
  ring

lemma trX (X : Matrix (Four d) (Four d) ℂ) : X.trace = ∑ b, ∑ c, Yc X (b, c) (b, c) := by
  simp only [Matrix.trace, Matrix.diag, Yc, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma trMid (X : Matrix (Four d) (Four d) ℂ) :
    (middleProjector d * X).trace = (d : ℂ)⁻¹ * ∑ b, ∑ b', Yc X (b', b') (b, b) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, mid_entry, X7TW.Pm, X7TW.Phi, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, Yc, Fintype.sum_prod_type]
  simp only [ite_and, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]

end X7PS

-- ===== p21s/S8 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma re_aux (hd : 0 < d) (y : ℂ) :
    ((1 : ℂ) / (d : ℂ)^2 + y / (d : ℂ)^3).re = 1 / (d : ℝ)^2 + y.re / (d : ℝ)^3 := by
  have e : (1 : ℂ) / (d : ℂ)^2 + y / (d : ℂ)^3 = ((1 / (d : ℝ)^2 : ℝ) : ℂ) + y * ((1 / (d : ℝ)^3 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.add_re, Complex.ofReal_re, Complex.re_mul_ofReal]
  ring

theorem gain_val (H : HaarLaw d) (hd : 2 ≤ d) (X : Matrix (Four d) (Four d) ℂ) (hc : SeedCommutes X)
    (ht : X.trace = (d : ℂ)^2) :
    gain H (covariantDensity X) = ((lambdaG d * X).trace).re := by
  have hd0 : 0 < d := by omega
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  obtain ⟨x, y, hxy⟩ := Y_form hd X hc
  have hxy' : YForm X x y := hxy
  rw [gain]
  simp_rw [gk_eq X x y hxy']
  rw [red H _ (gK_cont hd0 x y), int_gK H hd]
  have hT : X.trace = x * (d : ℂ)^2 + y * d := by
    rw [trX]
    simp only [hxy, and_self, if_true, mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
    ring
  have hM : (middleProjector d * X).trace = (d : ℂ)⁻¹ * (x * d + y * (d : ℂ)^2) := by
    rw [trMid]
    simp only [hxy, and_self, if_true, mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
    ring
  have hG : (lambdaG d * X).trace = (((d : ℂ)^2 * ((d : ℂ)^2 - 1))⁻¹) *
      ((1 - 2 / (d : ℂ)^2) * X.trace + (middleProjector d * X).trace) := by
    rw [lambdaG, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.one_mul, smul_eq_mul, smul_eq_mul]
  have hx : x = 1 - y / d := by
    have h := ht.symm.trans hT
    have h2 : x * d = d - y := by
      apply mul_left_cancel₀ hdC
      linear_combination -h
    field_simp
    linear_combination h2
  have hdd := dsq_ne hd
  have hGv : (lambdaG d * X).trace = 1 / (d : ℂ)^2 + y / (d : ℂ)^3 := by
    rw [hG, hM, ht, hx]
    field_simp
    ring
  rw [hGv, re_aux hd0, hx]
  have : (1 - y / (d : ℂ)).re = 1 - y.re / d := by
    rw [Complex.sub_re, Complex.one_re, Complex.div_natCast_re]
  rw [this]
  field_simp
  ring

end X7PS

-- ===== p21s/S9 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7PS
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma ins_cont {T : Type*} [TopologicalSpace T] {R : T → Matrix (Four d) (Four d) ℂ}
    {U : T → Matrix (Wire d) (Wire d) ℂ} {ρ : T → Matrix (Wire d) (Wire d) ℂ}
    (hR : Continuous R) (hU : Continuous U) (hρ : Continuous ρ) :
    Continuous fun t => (fun a anew => ∑ e : Wire d, ∑ enew : Wire d,
      (∑ b : Wire d, ∑ c : Wire d, ∑ bnew : Wire d, ∑ cnew : Wire d,
        U t b c * R t ((a, b), (c, e)) ((anew, bnew), (cnew, enew)) * conj (U t bnew cnew)) * ρ t e enew :
        Matrix (Wire d) (Wire d) ℂ) := by
  refine continuous_matrix fun a anew => ?_
  refine continuous_finset_sum _ fun e _ => continuous_finset_sum _ fun enew _ => ?_
  refine Continuous.mul ?_ (hρ.matrix_elem _ _)
  refine continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun bn _ => continuous_finset_sum _ fun cn _ => ?_
  exact ((hU.matrix_elem _ _).mul (hR.matrix_elem _ _)).mul
    (Complex.continuous_conj.comp (hU.matrix_elem _ _))

lemma pk_cont (X : Matrix (Four d) (Four d) ℂ) :
    Continuous fun t : EuclideanSpace ℂ (Wire d) × (SU d × SU d) =>
      pureKernel (covariantDensity X t.2.2) t.2.1 t.1 := by
  have hR : Continuous fun t : EuclideanSpace ℂ (Wire d) × (SU d × SU d) => covariantDensity X t.2.2 :=
    (X7P21.cD_cont X).comp (continuous_snd.comp continuous_snd)
  have hU : Continuous fun t : EuclideanSpace ℂ (Wire d) × (SU d × SU d) => unitaryMatrix t.2.1 :=
    X7P21.val_cont.comp (continuous_fst.comp continuous_snd)
  have hψ : Continuous fun t : EuclideanSpace ℂ (Wire d) × (SU d × SU d) => (WithLp.ofLp t.1 : Wire d → ℂ) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Wire d => ℂ)).comp continuous_fst
  have hρ : Continuous fun t : EuclideanSpace ℂ (Wire d) × (SU d × SU d) => pureDensity t.1 := by
    refine continuous_matrix fun a b => ?_
    simp only [pureDensity, Matrix.of_apply]
    exact ((continuous_apply a).comp hψ).mul (Complex.continuous_conj.comp ((continuous_apply b).comp hψ))
  have hv : Continuous fun t : EuclideanSpace ℂ (Wire d) × (SU d × SU d) =>
      (WithLp.ofLp (act (unitaryMatrix t.2.1) t.1) : Wire d → ℂ) := by
    simp only [act]
    exact hU.matrix_mulVec hψ
  have hM := ins_cont hR hU hρ
  unfold pureKernel
  refine Complex.continuous_re.comp ?_
  simp only [qf_def]
  exact (hv.star).dotProduct (hM.matrix_mulVec hv)

lemma cpt_int {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    {μ : Measure T} [IsFiniteMeasure μ] {f : T → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem inst (H : HaarLaw d) (hd : 2 ≤ d) (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef)
    (hc : SeedCommutes X) (ht : X.trace = (d : ℂ)^2) (hd0 : 0 < d) :
    IsHaarCombInstrument H hd0 (covariantDensity X) := by
  haveI := H.probability
  haveI : BorelSpace (Matrix (Four d) (Four d) ℂ) := ⟨rfl⟩
  refine ⟨(X7P21.cD_cont X).measurable, fun V => ?_, X7P21.integrable_of_cont H (X7P21.cD_cont X),
    fun i j => X7P21.integrable_of_cont H ((X7P21.cD_cont X).matrix_elem i j),
    (X7P21.main d hd H X hX hc).2 ht, ?_, ?_, ?_⟩
  · exact hX.mul_mul_conjTranspose_same _
  · simp_rw [fk_eq]
    exact cpt_int ((gF_cont X).comp pair_cont)
  · obtain ⟨x, y, hxy⟩ := Y_form hd X hc
    simp_rw [gk_eq X x y hxy]
    exact cpt_int ((gK_cont hd0 x y).comp pair_cont)
  · set g := fun U : Matrix.unitaryGroup (Fin d) ℂ => act (U : Matrix (Fin d) (Fin d) ℂ) (ket ⟨0, hd0⟩)
    have hg : Continuous g := QuditFidelity.haarState_continuous d hd0
    haveI : IsFiniteMeasure (Schur.unitaryHaar d) := ⟨by
      rw [show (Schur.unitaryHaar d) Set.univ = 1 from Measure.haarMeasure_self]; simp⟩
    have e : (QuditFidelity.haarPureStateLaw d hd0).prod (H.law.prod H.law) =
        ((Schur.unitaryHaar d).prod (H.law.prod H.law)).map (Prod.map g id) := by
      rw [QuditFidelity.haarPureStateLaw, ← Measure.map_prod_map _ _ hg.measurable measurable_id, Measure.map_id]
    rw [e]
    refine (integrable_map_measure (pk_cont X).aestronglyMeasurable
      (hg.measurable.prodMap measurable_id).aemeasurable).mpr ?_
    exact cpt_int ((pk_cont X).comp (hg.prodMap continuous_id))

end X7PS

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

open QAlgorithms.Papers.Independent.Claimed50.P21 in
theorem X7_scoreOperators (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d)
    (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef)
    (hc : SeedCommutes X) (ht : X.trace = (d : ℂ)^2) :
    (lambdaF d).PosSemidef ∧ (lambdaG d).PosSemidef ∧
    lambdaG d = gainBellContraction (lambdaF d) ∧
    IsHaarCombInstrument H (by omega) (covariantDensity X) ∧
    channelScore H (covariantDensity X) = ((lambdaF d * X).trace).re ∧
    gain H (covariantDensity X) = ((lambdaG d * X).trace).re ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      p * gain H (covariantDensity X) + (1-p) * channelScore H (covariantDensity X) =
        ((((p : ℂ) • lambdaG d + ((1-p : ℝ) : ℂ) • lambdaF d) * X).trace).re) := by
  have hF := X7PS.score H hd X
  have hG := X7PS.gain_val H hd X hc ht
  refine ⟨X7PS.lamF_psd hd, X7PS.lamG_psd hd, X7PS.bell hd, X7PS.inst H hd X hX hc ht _, hF, hG,
    fun p _ _ => ?_⟩
  rw [hF, hG, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

-- ===== p21a/UT =====
open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator
noncomputable section
namespace X7UT
open X7TW

abbrev UG (d : ℕ) := ↥(Matrix.unitaryGroup (Fin d) ℂ)


variable {d : ℕ}

lemma uunit_l (V : UG d) : (V.val)ᴴ * V.val = 1 := by
  have := V.2
  rw [Matrix.mem_unitaryGroup_iff'] at this; exact this

lemma uunit_r (V : UG d) : V.val * (V.val)ᴴ = 1 := by
  have := V.2
  rw [Matrix.mem_unitaryGroup_iff] at this; exact this

def usinv (W : UG d) : UG d := ⟨(W.val)ᴴ, by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  exact uunit_l W⟩

lemma uval_cont : Continuous (fun V : UG d => V.val) := continuous_subtype_val

lemma uK_cont : Continuous (fun V : UG d => K V.val) :=
  continuous_matrix fun p q => by
    simp only [K, Matrix.kroneckerMap_apply, Matrix.map_apply]
    exact (uval_cont.matrix_elem _ _).mul (Complex.continuous_conj.comp (uval_cont.matrix_elem _ _))

lemma uK_Phi (V : UG d) : K V.val * Phi d = Phi d := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  have hu := congrFun (congrFun (uunit_r V) p1) p2
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hu
  simp only [K, Phi, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  by_cases hq : q1 = q2
  · simp only [hq, and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← hu]; rfl
  · simp [hq]

lemma uPhi_K (V : UG d) : Phi d * K V.val = Phi d := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  have hu := congrFun (congrFun (uunit_l V) q2) q1
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

lemma uKct_Phi_K (V : UG d) : (K V.val)ᴴ * Phi d * K V.val = Phi d := by
  have : (K V.val)ᴴ * Phi d = Phi d := by
    rw [← Phi_ct, ← Matrix.conjTranspose_mul, uPhi_K, Phi_ct]
  rw [this, uPhi_K]

section utwirl
variable [MeasurableSpace (UG d)] [BorelSpace (UG d)] (μ : Measure (UG d)) [IsProbabilityMeasure μ]
  (hinv : ∀ (W : UG d) (f : UG d → ℂ), Continuous f → ∫ V, f (W * V) ∂μ = ∫ V, f V ∂μ)

/-- entrywise utwirl -/
def uT2 (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => ∫ V, (K V.val * M * (K V.val)ᴴ) p q ∂μ

omit [MeasurableSpace (UG d)] [BorelSpace (UG d)] in
lemma uF_cont (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Continuous fun V : UG d => K V.val * M * (K V.val)ᴴ :=
  (uK_cont.matrix_mul continuous_const).matrix_mul uK_cont.matrix_conjTranspose

lemma ucint {f : UG d → ℂ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma usandwich_gen {n : Type*} [Fintype n] (F : UG d → Matrix n n ℂ) (hF : Continuous F)
    (A B : Matrix n n ℂ) :
    A * (Matrix.of fun r s => ∫ V, F V r s ∂μ) * B = Matrix.of fun p q => ∫ V, (A * F V * B) p q ∂μ := by
  ext p q
  simp only [Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun s _ => ucint μ (show Continuous fun V => (∑ r, A p r * F V r s) * B s q from
    (continuous_finsetSum _ fun r _ => continuous_const.mul (hF.matrix_elem r s)).mul
      continuous_const))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_mul_const, integral_finsetSum _ (fun r _ => ucint μ
    (show Continuous fun V => A p r * F V r s from continuous_const.mul (hF.matrix_elem r s)))]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul]

lemma uT2_sandwich (M A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    A * uT2 μ M * B = Matrix.of fun p q => ∫ V, (A * (K V.val * M * (K V.val)ᴴ) * B) p q ∂μ :=
  usandwich_gen μ _ (uF_cont M) A B

include hinv in
lemma uT2_comm (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (W : UG d) :
    uT2 μ M * K W.val = K W.val * uT2 μ M := by
  have hKW : K W.val * (K W.val)ᴴ = 1 := by rw [K_ct, ← K_mul, uunit_r, K_one]
  have h1 : (K W.val)ᴴ * uT2 μ M * K W.val = uT2 μ M := by
    rw [uT2_sandwich]
    ext p q
    simp only [Matrix.of_apply, uT2]
    have := hinv (usinv W) (fun V => (K V.val * M * (K V.val)ᴴ) p q) ((uF_cont M).matrix_elem p q)
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    simp only
    have e : (usinv W * V : UG d).val = (W.val)ᴴ * V.val := rfl
    rw [e, K_mul, ← K_ct, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  calc uT2 μ M * K W.val = K W.val * ((K W.val)ᴴ * uT2 μ M * K W.val) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKW, Matrix.one_mul]
    _ = K W.val * uT2 μ M := by rw [h1]

lemma utrace_int {n : Type*} [Fintype n] (G : UG d → Matrix n n ℂ) (hG : Continuous G) :
    (Matrix.of fun p q => ∫ V, G V p q ∂μ).trace = ∫ V, (G V).trace ∂μ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [integral_finsetSum _ (fun p _ => ucint μ (hG.matrix_elem p p))]

lemma uT2_trace (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (uT2 μ M).trace = M.trace := by
  rw [uT2, utrace_int μ _ (uF_cont M)]
  have : ∀ V : UG d, (K V.val * M * (K V.val)ᴴ).trace = M.trace := fun V => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, K_ct, ← K_mul, uunit_l, K_one, Matrix.one_mul]
  simp only [this, integral_const, probReal_univ, one_smul]

lemma uT2_s (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (Phi d * uT2 μ M).trace = (Phi d * M).trace := by
  have := uT2_sandwich μ M (Phi d) 1
  rw [Matrix.mul_one] at this
  rw [this, utrace_int μ _ (((continuous_const.matrix_mul (uF_cont M)).matrix_mul continuous_const))]
  have h : ∀ V : UG d, (Phi d * (K V.val * M * (K V.val)ᴴ) * 1).trace = (Phi d * M).trace := fun V => by
    rw [Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, uKct_Phi_K]
  simp only [h, integral_const, probReal_univ, one_smul]

include hinv in
theorem utwirl (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    uT2 μ M = ((M.trace - (Phi d * M).trace / d) / ((d : ℂ) ^ 2 - 1)) • (1 : Matrix _ _ ℂ) +
      (((Phi d * M).trace - M.trace / d) / ((d : ℂ) ^ 2 - 1)) • Phi d := by
  obtain ⟨x, y, hxy⟩ := commutant hd (uT2 μ M) fun V hV => uT2_comm μ hinv M ⟨V, (Matrix.mem_specialUnitaryGroup_iff.mp hV).1⟩
  have ht := uT2_trace μ M
  have hs := uT2_s μ M
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

end utwirl

section
variable [MeasurableSpace (UG d)] [BorelSpace (UG d)] (μ : Measure (UG d)) [IsProbabilityMeasure μ]
  (hinv : ∀ (W : UG d) (f : UG d → ℂ), Continuous f → ∫ V, f (W * V) ∂μ = ∫ V, f V ∂μ)
include hinv

theorem utwirl_entry (hd : 2 ≤ d) (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (p q : Fin d × Fin d) :
    ∫ V, (K V.val * M * (K V.val)ᴴ) p q ∂μ = ca M * (if p = q then 1 else 0) + cb M * Phi d p q := by
  have := congrFun (congrFun (utwirl μ hinv hd M) p) q
  simp only [uT2, Matrix.of_apply] at this
  rw [this]
  simp [ca, cb, Matrix.one_apply]

end

section
variable [MeasurableSpace (UG d)] [BorelSpace (UG d)] (μ : Measure (UG d)) [IsProbabilityMeasure μ]
  (hinv : ∀ (W : UG d) (f : UG d → ℂ), Continuous f → ∫ V, f (W * V) ∂μ = ∫ V, f V ∂μ)
include hinv

theorem uwg (hd : 2 ≤ d) (a b c e : Fin d × Fin d) :
    ∫ V, K V.val a b * conj (K V.val c e) ∂μ =
      Pm d a c * Pm d b e + Qm d a c * Qm d b e / ((d : ℂ) ^ 2 - 1) := by
  have h := utwirl_entry μ hinv hd (Matrix.single b e (1 : ℂ)) a c
  have e1 : ∀ V : UG d, (K V.val * Matrix.single b e (1 : ℂ) * (K V.val)ᴴ) a c =
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

end

end X7UT

-- ===== p21a/A1 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7AF
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21 X7UT

variable {d : ℕ}

instance : IsProbabilityMeasure (Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

instance uhaarInv : (Schur.unitaryHaar d).IsMulLeftInvariant := by
  unfold Schur.unitaryHaar; infer_instance

lemma uhinv : ∀ (W : UG d) (f : UG d → ℂ), Continuous f →
    ∫ V, f (W * V) ∂(Schur.unitaryHaar d) = ∫ V, f V ∂(Schur.unitaryHaar d) :=
  fun W f _ => integral_mul_left_eq_self f W

lemma psi_entry (hd : 0 < d) (U : UG d) (e : Fin d) :
    (act (U : Matrix (Fin d) (Fin d) ℂ) (ket ⟨0, hd⟩)) e = U.val e ⟨0, hd⟩ := by
  simp [act, ket, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

theorem moment (hd : 0 < d) (e c e' c' : Fin d) :
    ∫ U, U.val e ⟨0, hd⟩ * U.val c' ⟨0, hd⟩ * conj (U.val c ⟨0, hd⟩) * conj (U.val e' ⟨0, hd⟩)
      ∂(Schur.unitaryHaar d) =
      ((if e = c ∧ c' = e' then 1 else 0) + (if e = e' ∧ c' = c then 1 else 0)) / ((d : ℂ) * (d + 1)) := by
  rcases Nat.lt_or_ge d 2 with h1 | h2
  · obtain rfl : d = 1 := by omega
    have hs : ∀ a b : Fin 1, a = b := fun a b => Subsingleton.elim a b
    obtain rfl : c = e := hs _ _
    obtain rfl : e' = c := hs _ _
    obtain rfl : c' = e' := hs _ _
    have ho : (⟨0, hd⟩ : Fin 1) = c' := hs _ _
    rw [ho]
    have hU : ∀ U : UG 1, U.val c' c' * conj (U.val c' c') = 1 := by
      intro U
      have := congrFun (congrFun (uunit_l U) c') c'
      have h0 : (0 : Fin 1) = c' := hs _ _
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.star_def,
        Fin.sum_univ_one, h0] at this
      rw [mul_comm]; exact this
    have : ∀ U : UG 1, U.val c' c' * U.val c' c' * conj (U.val c' c') * conj (U.val c' c') = 1 := by
      intro U
      linear_combination (U.val c' c' * conj (U.val c' c') + 1) * hU U
    simp only [this, integral_const, probReal_univ, one_smul, and_self, if_true]
    norm_num
  · set o : Fin d := ⟨0, hd⟩
    have h := uwg (Schur.unitaryHaar d) uhinv h2 (e, c) (o, o) (e', c') (o, o)
    have e1 : ∀ U : UG d, X7TW.K U.val (e, c) (o, o) * conj (X7TW.K U.val (e', c') (o, o)) =
        U.val e o * U.val c' o * conj (U.val c o) * conj (U.val e' o) := by
      intro U
      simp only [X7TW.K, Matrix.kroneckerMap_apply, Matrix.map_apply, map_mul, Complex.conj_conj]
      ring
    simp_rw [e1] at h
    rw [h]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (show d + 1 ≠ 0 by omega)
    have hd2 : (d : ℂ) ^ 2 - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast h2
      intro h
      have h' : ((d : ℝ)^2 - 1 : ℝ) = 0 := by exact_mod_cast h
      nlinarith
    have hd3 : (d : ℂ) - 1 ≠ 0 := by
      intro h; apply hd2; linear_combination ((d : ℂ) + 1) * h
    have hsq : (d : ℂ) ^ 2 - 1 = ((d : ℂ) - 1) * ((d : ℂ) + 1) := by ring
    simp only [X7TW.Pm, X7TW.Qm, X7TW.Phi, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, smul_eq_mul, Prod.mk.injEq, and_self, if_true]
    rw [hsq]
    simp only [show (c' = e') ↔ (e' = c') from eq_comm, show (c' = c) ↔ (c = c') from eq_comm]
    generalize (if e = c ∧ e' = c' then (1 : ℂ) else 0) = X
    generalize (if e = e' ∧ c = c' then (1 : ℂ) else 0) = Y
    field_simp
    ring

end X7AF

-- ===== p21a/A2 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7AF
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21 X7UT

variable {d : ℕ}

lemma qf_def' {I : Type*} [Fintype I] (v : I → ℂ) (M : Matrix I I ℂ) :
    Measurements.quadraticFunctional v M = star v ⬝ᵥ (M *ᵥ v) := rfl

lemma pK_exp (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) (ψ : EuclideanSpace ℂ (Wire d)) :
    pureKernel R4 U ψ = (∑ a, ∑ a', ∑ c', ∑ e, ∑ e', ∑ c,
      conj (unitaryMatrix U a c) * unitaryMatrix U a' c' * linkedChoi R4 U (a, e) (a', e') *
        (ψ e * ψ c' * conj (ψ c) * conj (ψ e'))).re := by
  rw [pureKernel, qf_def']
  congr 1
  simp only [dotProduct, Matrix.mulVec, act, insertedOutput, pureDensity, Matrix.of_apply, Pi.star_apply,
    Complex.star_def, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun c' _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c _ => ?_
  ring

def T1 (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) : ℂ :=
  ∑ a, ∑ a', ∑ c', ∑ c, conj (unitaryMatrix U a c) * unitaryMatrix U a' c' * linkedChoi R4 U (a, c) (a', c')

def T2 (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) : ℂ :=
  ∑ a, ∑ e, linkedChoi R4 U (a, e) (a, e)

lemma pK_cont (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    Continuous fun ψ : EuclideanSpace ℂ (Wire d) => pureKernel R4 U ψ := by
  have hψ : Continuous fun ψ : EuclideanSpace ℂ (Wire d) => (WithLp.ofLp ψ : Wire d → ℂ) :=
    PiLp.continuous_ofLp (p := 2) (β := fun _ : Wire d => ℂ)
  have hρ : Continuous fun ψ : EuclideanSpace ℂ (Wire d) => pureDensity ψ := by
    refine continuous_matrix fun a b => ?_
    simp only [pureDensity, Matrix.of_apply]
    exact ((continuous_apply a).comp hψ).mul (Complex.continuous_conj.comp ((continuous_apply b).comp hψ))
  have hv : Continuous fun ψ : EuclideanSpace ℂ (Wire d) =>
      (WithLp.ofLp (act (unitaryMatrix U) ψ) : Wire d → ℂ) := by
    simp only [act]
    exact continuous_const.matrix_mulVec hψ
  have hM := X7PS.ins_cont (continuous_const : Continuous fun _ : EuclideanSpace ℂ (Wire d) => R4)
    (continuous_const : Continuous fun _ : EuclideanSpace ℂ (Wire d) => unitaryMatrix U) hρ
  unfold pureKernel
  refine Complex.continuous_re.comp ?_
  simp only [qf_def']
  exact (hv.star).dotProduct (hM.matrix_mulVec hv)

lemma int_sum6 {G : Type*} [MeasurableSpace G] {μ : Measure G}
    (C : Fin d → Fin d → Fin d → Fin d → Fin d → Fin d → ℂ)
    (m : Fin d → Fin d → Fin d → Fin d → Fin d → Fin d → G → ℂ)
    (hm : ∀ a b c e f g, Integrable (m a b c e f g) μ) :
    ∫ W, (∑ a, ∑ b, ∑ c, ∑ e, ∑ f, ∑ g, C a b c e f g * m a b c e f g W) ∂μ =
      ∑ a, ∑ b, ∑ c, ∑ e, ∑ f, ∑ g, C a b c e f g * ∫ W, m a b c e f g W ∂μ := by
  have hI : ∀ a b c e f g, Integrable (fun W => C a b c e f g * m a b c e f g W) μ :=
    fun a b c e f g => (hm a b c e f g).const_mul _
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => integrable_finset_sum _ fun c _ =>
    integrable_finset_sum _ fun e _ => integrable_finset_sum _ fun f _ => integrable_finset_sum _ fun g _ =>
      hI a b c e f g]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ fun b _ => integrable_finset_sum _ fun c _ =>
    integrable_finset_sum _ fun e _ => integrable_finset_sum _ fun f _ => integrable_finset_sum _ fun g _ =>
      hI a b c e f g]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finset_sum _ fun c _ =>
    integrable_finset_sum _ fun e _ => integrable_finset_sum _ fun f _ => integrable_finset_sum _ fun g _ =>
      hI a b c e f g]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finset_sum _ fun e _ => integrable_finset_sum _ fun f _ => integrable_finset_sum _ fun g _ =>
      hI a b c e f g]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finset_sum _ fun f _ => integrable_finset_sum _ fun g _ => hI a b c e f g]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_finset_sum _ fun g _ => hI a b c e f g]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [integral_const_mul]

lemma ucint {f : UG d → ℂ} (hf : Continuous f) : Integrable f (Schur.unitaryHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma collapse (C : Fin d → Fin d → Fin d → Fin d → Fin d → Fin d → ℂ) (D : ℂ) :
    ∑ a, ∑ a', ∑ c', ∑ e, ∑ e', ∑ c, C a a' c' e e' c *
      (((if e = c ∧ c' = e' then 1 else 0) + (if e = e' ∧ c' = c then 1 else 0)) / D) =
    ((∑ a, ∑ a', ∑ c', ∑ c, C a a' c' c c' c) + ∑ a, ∑ a', ∑ c', ∑ e, C a a' c' e e c') / D := by
  have h1 : ∑ a, ∑ a', ∑ c', ∑ e, ∑ e', ∑ c, C a a' c' e e' c * (if e = c ∧ c' = e' then 1 else 0) =
      ∑ a, ∑ a', ∑ c', ∑ c, C a a' c' c c' c := by
    simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  have h2 : ∑ a, ∑ a', ∑ c', ∑ e, ∑ e', ∑ c, C a a' c' e e' c * (if e = e' ∧ c' = c then 1 else 0) =
      ∑ a, ∑ a', ∑ c', ∑ e, C a a' c' e e c' := by
    simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  have e : ∀ a a' c' e e' c, C a a' c' e e' c *
      (((if e = c ∧ c' = e' then 1 else 0) + (if e = e' ∧ c' = c then 1 else 0)) / D) =
      C a a' c' e e' c * (if e = c ∧ c' = e' then 1 else 0) / D +
        C a a' c' e e' c * (if e = e' ∧ c' = c then 1 else 0) / D := by
    intros; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_div, h1, h2]
  ring

lemma T2_eq (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    (∑ a, ∑ a', ∑ c', ∑ e, conj (unitaryMatrix U a c') * unitaryMatrix U a' c' * linkedChoi R4 U (a, e) (a', e)) =
      T2 R4 U := by
  unfold T2
  refine Finset.sum_congr rfl fun a _ => ?_
  have hu : ∀ a' : Wire d, ∑ c', conj (unitaryMatrix U a c') * unitaryMatrix U a' c' = if a' = a then 1 else 0 := by
    intro a'
    have := congrFun (congrFun (X7P21.unit_right U) a') a
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def] at this
    rw [← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have : ∀ a' : Wire d, ∑ c', ∑ e, conj (unitaryMatrix U a c') * unitaryMatrix U a' c' *
      linkedChoi R4 U (a, e) (a', e) = (if a' = a then 1 else 0) * ∑ e, linkedChoi R4 U (a, e) (a', e) := by
    intro a'
    rw [← hu a', Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem pure_avg (hd : 0 < d) (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    ∫ ψ, pureKernel R4 U ψ ∂(QuditFidelity.haarPureStateLaw d hd) =
      ((T1 R4 U + T2 R4 U) / ((d : ℂ) * (d + 1))).re := by
  rw [QuditFidelity.haarPureStateLaw, integral_map (QuditFidelity.haarState_continuous d hd).aemeasurable
    (pK_cont R4 U).aestronglyMeasurable]
  simp_rw [pK_exp, psi_entry hd]
  have hm : ∀ e c e' c' : Fin d, Continuous fun W : UG d =>
      W.val e ⟨0, hd⟩ * W.val c' ⟨0, hd⟩ * conj (W.val c ⟨0, hd⟩) * conj (W.val e' ⟨0, hd⟩) := by
    intro e c e' c'
    have h := fun a b : Fin d => (continuous_subtype_val (p := fun x => x ∈ Matrix.unitaryGroup (Fin d) ℂ)).matrix_elem a b
    exact (((h e _).mul (h c' _)).mul (Complex.continuous_conj.comp (h c _))).mul
      (Complex.continuous_conj.comp (h e' _))
  have hre := integral_re (μ := Schur.unitaryHaar d) (integrable_finset_sum Finset.univ fun a _ =>
    integrable_finset_sum Finset.univ fun a' _ => integrable_finset_sum Finset.univ fun c' _ => integrable_finset_sum Finset.univ fun e _ =>
    integrable_finset_sum Finset.univ fun e' _ => integrable_finset_sum Finset.univ fun c _ =>
      (ucint (hm e c e' c')).const_mul (conj (unitaryMatrix U a c) * unitaryMatrix U a' c' *
        linkedChoi R4 U (a, e) (a', e')))
  simp only [RCLike.re_to_complex] at hre
  rw [hre]
  congr 1
  rw [int_sum6 (μ := Schur.unitaryHaar d) (fun a a' c' e e' c => conj (unitaryMatrix U a c) * unitaryMatrix U a' c' *
      linkedChoi R4 U (a, e) (a', e'))
    (fun a a' c' e e' c W => W.val e ⟨0, hd⟩ * W.val c' ⟨0, hd⟩ * conj (W.val c ⟨0, hd⟩) * conj (W.val e' ⟨0, hd⟩))
    (fun _ _ _ e e' c => ucint (hm e c e' _))]
  simp only [moment hd]
  rw [collapse]
  congr 2
  rw [T2_eq]

end X7AF

-- ===== p21a/A3 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7AF
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21 X7UT

variable {d : ℕ}

lemma reord8 (f : Wire d → Wire d → Wire d → Wire d → Wire d → Wire d → Wire d → Wire d → ℂ) :
    ∑ a, ∑ b, ∑ x, ∑ c, ∑ a', ∑ b', ∑ x', ∑ c', f a b x c a' b' x' c' =
      ∑ a, ∑ a', ∑ c', ∑ c, ∑ b, ∑ x, ∑ b', ∑ x', f a b x c a' b' x' c' := by
  conv_lhs => arg 2; ext a; arg 2; ext v0; arg 2; ext v1; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext v0; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext v0; arg 2; ext v1; arg 2; ext v2; arg 2; ext v3; arg 2; ext v4; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext v0; arg 2; ext v1; arg 2; ext v2; arg 2; ext v3; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext v0; arg 2; ext v1; arg 2; ext v2; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext v0; arg 2; ext v1; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext v0; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext v0; arg 2; ext v1; arg 2; ext v2; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext v0; arg 2; ext v1; rw [Finset.sum_comm]

lemma T1_eq (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    T1 R4 U = Measurements.quadraticFunctional (fidelityVector U) R4 := by
  rw [qf_def', T1]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, fidelityVector, Fintype.sum_prod_type, Finset.mul_sum,
    linkedChoi, Complex.star_def, map_mul, Complex.conj_conj]
  conv_rhs => rw [reord8]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun c' _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun x' _ => ?_
  ring

end X7AF

-- ===== p21a/A4 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7AF
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21 X7UT

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma oD_T2 (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    outcomeDensity R4 U (((d : ℂ)⁻¹) • 1) = ((d : ℂ)⁻¹ * T2 R4 U).re := by
  rw [outcomeDensity, T2]
  congr 1
  simp only [insertedOutput, Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  ring

lemma fK_T1 (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    fidelityKernel R4 U = (T1 R4 U).re / (d : ℝ)^2 := by
  rw [fidelityKernel, T1_eq]

theorem pure_avg' (hd : 0 < d) (R4 : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    ∫ ψ, pureKernel R4 U ψ ∂(QuditFidelity.haarPureStateLaw d hd) =
      ((d : ℝ) * fidelityKernel R4 U + outcomeDensity R4 U (((d : ℂ)⁻¹) • 1)) / ((d : ℝ) + 1) := by
  rw [pure_avg hd, fK_T1, oD_T2]
  have e1 : (T1 R4 U + T2 R4 U) / ((d : ℂ) * (d + 1)) =
      (T1 R4 U + T2 R4 U) * ((((d : ℝ) * (d + 1))⁻¹ : ℝ) : ℂ) := by push_cast; ring
  have e2 : (d : ℂ)⁻¹ * T2 R4 U = T2 R4 U * ((((d : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.re_mul_ofReal, Complex.re_mul_ofReal, Complex.add_re]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- T2 as a continuous linear functional of the instrument matrix -/
def T2L (U : SU d) : Matrix (Four d) (Four d) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun R4 => T2 R4 U
      map_add' := fun A B => by
        simp only [T2, linkedChoi, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c A => by
        simp only [T2, linkedChoi, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun x' _ => ?_
        ring }

lemma reord6 (f : Wire d → Wire d → Wire d → Wire d → Wire d → Wire d → ℂ) :
    ∑ a, ∑ e, ∑ b, ∑ x, ∑ b', ∑ x', f a e b x b' x' = ∑ e, ∑ b, ∑ x, ∑ b', ∑ x', ∑ a, f a e b x b' x' := by
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext v0; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext v0; arg 2; ext v1; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext v0; arg 2; ext v1; arg 2; ext v2; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext v0; arg 2; ext v1; arg 2; ext v2; arg 2; ext v3; rw [Finset.sum_comm]

lemma T2_comb (R4 : Matrix (Four d) (Four d) ℂ) (hR : IsDeterministicTwoComb R4) (U : SU d) :
    T2 R4 U = d := by
  obtain ⟨_, Rone, _, h1, h2⟩ := hR
  rw [T2]
  simp only [linkedChoi]
  rw [reord6]
  have e : ∀ e b x b' x' : Wire d, (∑ a, unitaryMatrix U b x * R4 ((a, b), (x, e)) ((a, b'), (x', e)) *
      conj (unitaryMatrix U b' x')) =
      unitaryMatrix U b x * ((if b = b' then 1 else 0) * Rone (x, e) (x', e)) * conj (unitaryMatrix U b' x') := by
    intro e b x b' x'
    rw [← h1, Finset.mul_sum, Finset.sum_mul]
  simp only [e]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  have hu : ∀ x x' : Wire d, ∑ b, unitaryMatrix U b x * conj (unitaryMatrix U b x') = if x' = x then 1 else 0 := by
    intro x x'
    have := congrFun (congrFun (X7P21.unit_left U) x') x
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e2 : ∀ e : Wire d, ∑ b, ∑ x, ∑ x', unitaryMatrix U b x * Rone (x, e) (x', e) * conj (unitaryMatrix U b x') =
      1 := by
    intro e
    have h2e := h2 e e
    rw [if_pos rfl] at h2e
    rw [← h2e, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    have : ∀ x', ∑ b, unitaryMatrix U b x * Rone (x, e) (x', e) * conj (unitaryMatrix U b x') =
        (if x' = x then 1 else 0) * Rone (x, e) (x', e) := by
      intro x'
      rw [← hu x x', Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => arg 2; ext v0; arg 2; ext v1; rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end X7AF

-- ===== p21a/A5 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7AF
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21 X7UT

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma T2L_apply (U : SU d) (R4 : Matrix (Four d) (Four d) ℂ) : T2L U R4 = T2 R4 U := rfl

theorem oD_int (H : HaarLaw d) (hd : 0 < d) (R : SU d → Matrix (Four d) (Four d) ℂ)
    (hint : Integrable R H.law) (hcomb : IsDeterministicTwoComb (∫ V, R V ∂H.law)) (U : SU d) :
    ∫ V, outcomeDensity (R V) U (((d : ℂ)⁻¹) • 1) ∂H.law = 1 := by
  simp_rw [oD_T2]
  have hi : Integrable (fun V => (d : ℂ)⁻¹ * T2 (R V) U) H.law := by
    have := ((T2L U).integrable_comp hint).const_mul ((d : ℂ)⁻¹)
    simpa [T2L_apply] using this
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  rw [hre, integral_const_mul]
  have h2 : ∫ V, T2 (R V) U ∂H.law = T2 (∫ V, R V ∂H.law) U := by
    simp_rw [← T2L_apply]
    exact (T2L U).integral_comp_comm hint
  rw [h2, T2_comb _ hcomb U]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [inv_mul_cancel₀ this, Complex.one_re]

theorem avg (d : ℕ) (hd : 0 < d) (H : HaarLaw d)
    (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : IsHaarCombInstrument H hd R) :
    averagePureFidelity H hd R =
      (d : ℝ)/((d : ℝ)+1) * channelScore H R + 1/((d : ℝ)+1) := by
  haveI := H.probability
  haveI : IsProbabilityMeasure (QuditFidelity.haarPureStateLaw d hd) :=
    ⟨QuditFidelity.haarPureStateLaw_univ d hd⟩
  obtain ⟨_, _, hint, _, hcomb, hfid, _, hpure⟩ := hR
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [averagePureFidelity, integral_prod_symm _ hpure]
  simp_rw [pure_avg' hd]
  have hI := hpure.integral_prod_right
  have hoD : Integrable (fun s : SU d × SU d => outcomeDensity (R s.2) s.1 (((d : ℂ)⁻¹) • 1)) (H.law.prod H.law) := by
    have h := (hI.const_mul ((d : ℝ) + 1)).sub (hfid.const_mul (d : ℝ))
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Pi.sub_apply]
    rw [pure_avg' hd]
    field_simp
    ring
  have e : ∀ s : SU d × SU d, ((d : ℝ) * fidelityKernel (R s.2) s.1 + outcomeDensity (R s.2) s.1 (((d : ℂ)⁻¹) • 1)) / ((d : ℝ) + 1) =
      (d : ℝ) / ((d : ℝ) + 1) * fidelityKernel (R s.2) s.1 + 1 / ((d : ℝ) + 1) * outcomeDensity (R s.2) s.1 (((d : ℂ)⁻¹) • 1) := by
    intro s; field_simp
  simp_rw [e]
  rw [integral_add (hfid.const_mul _) (hoD.const_mul _), integral_const_mul, integral_const_mul,
    integral_prod _ hoD]
  simp only [oD_int H hd R hint hcomb, integral_const, probReal_univ, one_smul, mul_one, channelScore]

end X7AF

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

open QAlgorithms.Papers.Independent.Claimed50.P21 in
theorem X7_avgFid (d : ℕ) (hd : 0 < d) (H : HaarLaw d)
    (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : IsHaarCombInstrument H hd R) :
    averagePureFidelity H hd R =
      (d : ℝ)/((d : ℝ)+1) * channelScore H R + 1/((d : ℝ)+1) :=
  X7AF.avg d hd H R hR

-- ===== p21c/R1 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma mp_left (H : HaarLaw d) (V : SU d) : MeasurePreserving (fun U : SU d => V * U) H.law H.law :=
  ⟨(continuous_const.mul continuous_id).measurable, H.left_invariant V⟩

lemma me_left (V : SU d) : MeasurableEmbedding (fun U : SU d => V * U) :=
  (Homeomorph.mulLeft V).measurableEmbedding

/-- left invariance for arbitrary integrands -/
lemma int_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : HaarLaw d) (V : SU d)
    (f : SU d → E) : ∫ U, f (V * U) ∂H.law = ∫ U, f U ∂H.law :=
  (mp_left H V).integral_comp (me_left V) f

lemma um_mul (A B : SU d) : unitaryMatrix (A * B) = unitaryMatrix A * unitaryMatrix B := rfl
lemma um_one : unitaryMatrix (1 : SU d) = 1 := rfl

lemma rep_mul (A B C D : SU d) :
    representation (A * B) (C * D) = representation A C * representation B D := by
  unfold representation
  rw [um_mul, um_mul, Matrix.map_mul, Matrix.map_mul, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
    Matrix.mul_kronecker_mul]

lemma cA_mul (A B C D : SU d) (M : Matrix (Four d) (Four d) ℂ) :
    covarianceAction (A * B) (C * D) M = covarianceAction A C (covarianceAction B D M) := by
  unfold covarianceAction
  rw [rep_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma rep_cont : Continuous fun t : SU d × SU d => representation t.1 t.2 := by
  unfold representation
  have hv := X7P21.val_cont (d := d)
  have hb : Continuous fun V : SU d => (unitaryMatrix V).map conj := hv.matrix_map Complex.continuous_conj
  exact X7P21.kron_cont (X7P21.kron_cont (hv.comp continuous_fst) (hb.comp continuous_fst))
    (X7P21.kron_cont (hv.comp continuous_snd) (hb.comp continuous_snd))

lemma rep_bdd : ∃ C : ℝ, ∀ V W : SU d, ‖representation V W‖ ≤ C ∧ ‖(representation V W)ᴴ‖ ≤ C := by
  have h1 := (isCompact_univ.image (rep_cont (d := d))).isBounded
  have h2 := (isCompact_univ.image (rep_cont (d := d)).matrix_conjTranspose).isBounded
  obtain ⟨C1, hC1⟩ := h1.exists_norm_le
  obtain ⟨C2, hC2⟩ := h2.exists_norm_le
  refine ⟨max C1 C2, fun V W => ⟨?_, ?_⟩⟩
  · exact (hC1 _ ⟨(V, W), Set.mem_univ _, rfl⟩).trans (le_max_left _ _)
  · exact (hC2 _ ⟨(V, W), Set.mem_univ _, rfl⟩).trans (le_max_right _ _)

lemma cA_integrable (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law)
    (a b : SU d → SU d) (ha : Continuous a) (hb : Continuous b) :
    Integrable (fun W => covarianceAction (a W) (b W) (R W)) H.law := by
  obtain ⟨C, hC⟩ := rep_bdd (d := d)
  have hr : Continuous fun W => representation (a W) (b W) := rep_cont.comp (ha.prodMk hb)
  refine Integrable.mono' (hR.norm.const_mul (C * C)) ?_ (Filter.Eventually.of_forall fun W => ?_)
  · unfold covarianceAction
    exact (hr.aestronglyMeasurable.mul hR.aestronglyMeasurable).mul hr.matrix_conjTranspose.aestronglyMeasurable
  · unfold covarianceAction
    calc ‖representation (a W) (b W) * R W * (representation (a W) (b W))ᴴ‖
        ≤ ‖representation (a W) (b W) * R W‖ * ‖(representation (a W) (b W))ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖representation (a W) (b W)‖ * ‖R W‖ * ‖(representation (a W) (b W))ᴴ‖ := by
          gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ C * ‖R W‖ * C := by
          have h := hC (a W) (b W)
          have hC0 : 0 ≤ C := (norm_nonneg _).trans h.1
          exact mul_le_mul (mul_le_mul_of_nonneg_right h.1 (norm_nonneg _)) h.2 (norm_nonneg _)
            (mul_nonneg hC0 (norm_nonneg _))
      _ = C * C * ‖R W‖ := by ring

end X7CR

-- ===== p21c/R2 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

def Yr (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) : Matrix (Four d) (Four d) ℂ :=
  ∫ W, covarianceAction 1 W (R W) ∂H.law

lemma cA_split (L C D : SU d) (M : Matrix (Four d) (Four d) ℂ) :
    covarianceAction L (C * D) M = covarianceAction L C (covarianceAction 1 D M) := by
  rw [← cA_mul, mul_one]

lemma cA_int (H : HaarLaw d) (L C : SU d) (g : SU d → Matrix (Four d) (Four d) ℂ) (hg : Integrable g H.law) :
    ∫ W, covarianceAction L C (g W) ∂H.law = covarianceAction L C (∫ W, g W ∂H.law) := by
  unfold covarianceAction
  exact X7P21.int_conj _ _ g hg

lemma inner (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law) (L V : SU d) :
    ∫ W, covarianceAction L W (R (L⁻¹ * V * W)) ∂H.law = covarianceAction L (V⁻¹ * L) (Yr H R) := by
  rw [← int_left H (V⁻¹ * L)]
  have e : ∀ W : SU d, L⁻¹ * V * (V⁻¹ * L * W) = W := fun W => by group
  simp only [e]
  simp_rw [cA_split L (V⁻¹ * L)]
  exact cA_int H _ _ (fun U => covarianceAction 1 U (R U))
    (cA_integrable H R hR (fun _ => 1) (fun U => U) continuous_const continuous_id)

lemma twirl_eq (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law) (V : SU d) :
    twirl H R V = ∫ L, covarianceAction L (V⁻¹ * L) (Yr H R) ∂H.law := by
  unfold twirl
  simp_rw [inner H R hR]

lemma cAc (M : Matrix (Four d) (Four d) ℂ) (a b : SU d → SU d) (ha : Continuous a) (hb : Continuous b) :
    Continuous fun L => covarianceAction (a L) (b L) M := by
  unfold covarianceAction
  have hr : Continuous fun L => representation (a L) (b L) := rep_cont.comp (ha.prodMk hb)
  exact (hr.matrix_mul continuous_const).matrix_mul hr.matrix_conjTranspose

lemma twirl_cov (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law) (V : SU d) :
    twirl H R V = covariantDensity (twirl H R 1) V := by
  haveI := H.probability
  rw [twirl_eq H R hR, twirl_eq H R hR, covariantDensity]
  have hi : Integrable (fun L : SU d => covarianceAction L (1⁻¹ * L) (Yr H R)) H.law :=
    X7P21.integrable_of_cont H (cAc _ _ _ continuous_id (continuous_const.mul continuous_id))
  rw [← cA_int H _ _ _ hi]
  rw [← int_left H V]
  congr 1
  ext1 L
  rw [← cA_mul]
  congr 1
  simp

end X7CR

-- ===== p21c/R3 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma X_eq (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law) :
    twirl H R 1 = ∫ L, covarianceAction L L (Yr H R) ∂H.law := by
  rw [twirl_eq H R hR]
  simp

lemma hcL (M : Matrix (Four d) (Four d) ℂ) : Continuous fun L : SU d => covarianceAction L L M :=
  cAc M (fun L => L) (fun L => L) continuous_id continuous_id

lemma cA_psd (L W : SU d) (M : Matrix (Four d) (Four d) ℂ) (hM : M.PosSemidef) :
    (covarianceAction L W M).PosSemidef :=
  hM.mul_mul_conjTranspose_same _

lemma cA_unit (L W : SU d) : (representation L W)ᴴ * representation L W = 1 := X7P21.rep_unit L W

lemma cA_trace (L W : SU d) (M : Matrix (Four d) (Four d) ℂ) : (covarianceAction L W M).trace = M.trace := by
  unfold covarianceAction
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, cA_unit, Matrix.one_mul]

lemma Y_psd (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law)
    (hp : ∀ V, (R V).PosSemidef) : (Yr H R).PosSemidef :=
  X7P21.int_psd _ (cA_integrable H R hR (fun _ => 1) (fun U => U) continuous_const continuous_id)
    fun W => cA_psd _ _ _ (hp W)

lemma X_psd (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law)
    (hp : ∀ V, (R V).PosSemidef) : (twirl H R 1).PosSemidef := by
  rw [X_eq H R hR]
  exact X7P21.int_psd _ (X7P21.integrable_of_cont H (hcL _))
    fun L => cA_psd _ _ _ (Y_psd H R hR hp)

lemma X_inv (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law) (V : SU d) :
    covarianceAction V V (twirl H R 1) = twirl H R 1 := by
  rw [X_eq H R hR, ← cA_int H _ _ _ (X7P21.integrable_of_cont H (hcL _))]
  conv_rhs => rw [← int_left H V]
  congr 1
  ext1 L
  rw [cA_mul]

lemma X_comm (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law) :
    SeedCommutes (twirl H R 1) := by
  intro V
  have h := X_inv H R hR V
  unfold covarianceAction at h
  conv_lhs => rw [← h]
  rw [Matrix.mul_assoc, cA_unit, Matrix.mul_one]

lemma comb_trace (M : Matrix (Four d) (Four d) ℂ) (hM : IsDeterministicTwoComb M) : M.trace = (d : ℂ)^2 := by
  obtain ⟨_, Rone, _, h1, h2⟩ := hM
  have e : M.trace = ∑ b, ∑ c, ∑ e, ∑ a, M ((a, b), (c, e)) ((a, b), (c, e)) := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
  rw [e]
  simp only [h1, if_true, one_mul]
  have h3 : ∀ e : Wire d, ∑ c, Rone (c, e) (c, e) = 1 := fun e => by rw [h2]; simp
  have h5 : ∑ c, ∑ e, Rone (c, e) (c, e) = (d : ℂ) := by
    rw [Finset.sum_comm]; simp [h3]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h5]; ring

lemma X_trace (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law)
    (hc : IsDeterministicTwoComb (∫ V, R V ∂H.law)) : (twirl H R 1).trace = (d : ℂ)^2 := by
  haveI := H.probability
  rw [X_eq H R hR, ← X7P21.int_trace _ (X7P21.integrable_of_cont H (hcL _))]
  simp only [cA_trace, integral_const, probReal_univ, one_smul]
  rw [Yr, ← X7P21.int_trace _ (cA_integrable H R hR (fun _ => 1) (fun U => U) continuous_const continuous_id)]
  simp only [cA_trace]
  rw [X7P21.int_trace _ hR, comb_trace _ hc]

lemma X_cov (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law) (V L W : SU d) :
    covariantDensity (twirl H R 1) (L * V * W⁻¹) = covarianceAction L W (covariantDensity (twirl H R 1) V) := by
  unfold covariantDensity
  have h1 : L * V = (L * V * W⁻¹) * W := by group
  calc covarianceAction (L * V * W⁻¹) 1 (twirl H R 1)
      = covarianceAction (L * V * W⁻¹) 1 (covarianceAction W W (twirl H R 1)) := by rw [X_inv H R hR]
    _ = covarianceAction ((L * V * W⁻¹) * W) (1 * W) (twirl H R 1) := by rw [cA_mul]
    _ = covarianceAction (L * V) W (twirl H R 1) := by rw [← h1, one_mul]
    _ = covarianceAction L W (covarianceAction V 1 (twirl H R 1)) := by rw [← cA_mul, mul_one]

end X7CR

-- ===== p21c/R4 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma rep_K (L W : SU d) : representation L W = X7TW.K (unitaryMatrix L) ⊗ₖ X7TW.K (unitaryMatrix W) := rfl

lemma Pm_inv (V : SU d) : (X7TW.K (unitaryMatrix V))ᴴ * X7TW.Pm d * X7TW.K (unitaryMatrix V) = X7TW.Pm d := by
  rw [X7TW.Pm, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  exact X7TW.Kct_Phi_K (d := d) V

lemma KK_unit (V : SU d) : (X7TW.K (unitaryMatrix V))ᴴ * X7TW.K (unitaryMatrix V) = 1 := by
  rw [X7TW.K_ct, ← X7TW.K_mul, X7P21.unit_left, X7TW.K_one]

lemma Qm_inv (V : SU d) : (X7TW.K (unitaryMatrix V))ᴴ * X7TW.Qm d * X7TW.K (unitaryMatrix V) = X7TW.Qm d := by
  rw [X7TW.Qm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, KK_unit, Pm_inv]

lemma kron_conj (A B : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ) (M N : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ) :
    (A ⊗ₖ B)ᴴ * (M ⊗ₖ N) * (A ⊗ₖ B) = (Aᴴ * M * A) ⊗ₖ (Bᴴ * N * B) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

lemma lamF_inv (L W : SU d) : (representation L W)ᴴ * lambdaF d * representation L W = lambdaF d := by
  rw [X7PS.lamF_eq, rep_K, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, kron_conj, kron_conj, Qm_inv, Qm_inv, Pm_inv, Pm_inv]

lemma trF_inv (L W : SU d) (M : Matrix (Four d) (Four d) ℂ) :
    (lambdaF d * covarianceAction L W M).trace = (lambdaF d * M).trace := by
  unfold covarianceAction
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [lamF_inv]

def trL (A : Matrix (Four d) (Four d) ℂ) : Matrix (Four d) (Four d) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (A * M).trace
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c M => by rw [Matrix.mul_smul, Matrix.trace_smul]; rfl }

lemma trL_apply (A M : Matrix (Four d) (Four d) ℂ) : trL A M = (A * M).trace := rfl

lemma int_tr (H : HaarLaw d) (A : Matrix (Four d) (Four d) ℂ) (f : SU d → Matrix (Four d) (Four d) ℂ)
    (hf : Integrable f H.law) : ∫ V, (A * f V).trace ∂H.law = (A * ∫ V, f V ∂H.law).trace := by
  simp_rw [← trL_apply]
  exact (trL A).integral_comp_comm hf

lemma score_R (H : HaarLaw d) (hd : 2 ≤ d) (R : SU d → Matrix (Four d) (Four d) ℂ)
    (hfid : Integrable (fun t : SU d × SU d => fidelityKernel (R t.2) t.1) (H.law.prod H.law)) :
    channelScore H R = ∫ V, ((lambdaF d * R V).trace).re ∂H.law := by
  haveI := H.probability
  rw [channelScore, integral_prod_symm _ hfid]
  congr 1
  ext1 V
  exact X7PS.int_gF H hd (R V)

theorem score_X (H : HaarLaw d) (hd : 2 ≤ d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law)
    (hfid : Integrable (fun t : SU d × SU d => fidelityKernel (R t.2) t.1) (H.law.prod H.law)) :
    channelScore H (covariantDensity (twirl H R 1)) = channelScore H R := by
  haveI := H.probability
  rw [X7PS.score H hd, score_R H hd R hfid, X_eq H R hR, ← int_tr H _ _ (X7P21.integrable_of_cont H (hcL _))]
  simp only [trF_inv, integral_const, probReal_univ, one_smul]
  rw [Yr, ← int_tr H _ _ (cA_integrable H R hR (fun _ => 1) (fun U => U) continuous_const continuous_id)]
  simp only [trF_inv]
  have hi : Integrable (fun V => (lambdaF d * R V).trace) H.law := by
    simp_rw [← trL_apply]; exact (trL _).integrable_comp hR
  have := integral_re hi
  simp only [RCLike.re_to_complex] at this
  exact this.symm

end X7CR

-- ===== p21c/R5 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma T2_single (p q : Four d) (U : SU d) :
    X7AF.T2 (Matrix.single p q 1) U = (if p.1.1 = q.1.1 ∧ p.2.2 = q.2.2 then 1 else 0) *
      (unitaryMatrix U p.1.2 p.2.1 * conj (unitaryMatrix U q.1.2 q.2.1)) := by
  obtain ⟨⟨p3, p2⟩, ⟨p1, p0⟩⟩ := p
  obtain ⟨⟨q3, q2⟩, ⟨q1, q0⟩⟩ := q
  simp only [X7AF.T2, linkedChoi, Matrix.single_apply, Prod.mk.injEq]
  simp only [ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [@eq_comm _ q3 p3, @eq_comm _ q0 p0]
  by_cases h3 : p3 = q3 <;> by_cases h0 : p0 = q0 <;> simp [h3, h0]

lemma rep1W (W : SU d) (i k : Four d) : representation 1 W i k =
    (if i.1 = k.1 then 1 else 0) * (unitaryMatrix W i.2.1 k.2.1 * conj (unitaryMatrix W i.2.2 k.2.2)) := by
  simp only [representation, um_one, Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.one_apply, Prod.mk.injEq]
  obtain ⟨⟨i3, i2⟩, ⟨i1, i0⟩⟩ := i
  obtain ⟨⟨k3, k2⟩, ⟨k1, k0⟩⟩ := k
  by_cases h3 : i3 = k3 <;> by_cases h2 : i2 = k2 <;> simp [h3, h2]

lemma cA_single (W : SU d) (p q : Four d) (i j : Four d) :
    covarianceAction 1 W (Matrix.single p q 1) i j = representation 1 W i p * conj (representation 1 W j q) := by
  simp only [covarianceAction, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, Complex.star_def,
    ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]

lemma wsum (W : SU d) (k l : Wire d) : ∑ e, conj (unitaryMatrix W e k) * unitaryMatrix W e l = if k = l then 1 else 0 := by
  have := congrFun (congrFun (X7P21.unit_left W) k) l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def] at this
  exact this

lemma T2_cA_single (W U : SU d) (p q : Four d) :
    X7AF.T2 (covarianceAction 1 W (Matrix.single p q 1)) U = X7AF.T2 (Matrix.single p q 1) (U * W) := by
  rw [T2_single]
  obtain ⟨⟨p3, p2⟩, ⟨p1, p0⟩⟩ := p
  obtain ⟨⟨q3, q2⟩, ⟨q1, q0⟩⟩ := q
  simp only [X7AF.T2, linkedChoi, cA_single, rep1W, Prod.mk.injEq, um_mul, Matrix.mul_apply]
  simp only [map_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, Complex.conj_conj, ite_and, ite_mul, mul_ite,
    one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [@eq_comm _ q3 p3]
  by_cases h3 : p3 = q3
  · simp only [h3, if_true]
    have hf : (∑ x, ∑ x_1, ∑ x_2, unitaryMatrix U p2 x_1 *
        (unitaryMatrix W x_1 p1 * conj (unitaryMatrix W x p0) *
          (conj (unitaryMatrix W x_2 q1) * unitaryMatrix W x q0)) * conj (unitaryMatrix U q2 x_2)) =
        (∑ x, conj (unitaryMatrix W x p0) * unitaryMatrix W x q0) *
          ((∑ j, unitaryMatrix U p2 j * unitaryMatrix W j p1) *
            conj (∑ j, unitaryMatrix U q2 j * unitaryMatrix W j q1)) := by
      simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      conv_lhs => arg 2; ext v; rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [hf, wsum]
    by_cases h0 : p0 = q0 <;> simp [h0]
  · simp [h3]

end X7CR

-- ===== p21c/R6 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma cA_sum_smul (W : SU d) (M : Matrix (Four d) (Four d) ℂ) :
    covarianceAction 1 W M = ∑ p, ∑ q, M p q • covarianceAction 1 W (Matrix.single p q 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  unfold covarianceAction
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [show Matrix.single p q (M p q) = M p q • Matrix.single p q (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
    Matrix.mul_smul, Matrix.smul_mul]

lemma T2_cA (W U : SU d) (M : Matrix (Four d) (Four d) ℂ) :
    X7AF.T2 (covarianceAction 1 W M) U = X7AF.T2 M (U * W) := by
  rw [cA_sum_smul, ← X7AF.T2L_apply, map_sum]
  conv_rhs => rw [Matrix.matrix_eq_sum_single M, ← X7AF.T2L_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, X7AF.T2L_apply, T2_cA_single, show Matrix.single p q (M p q) = M p q • Matrix.single p q (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, X7AF.T2L_apply]

lemma sinv_eq (L : SU d) : X7P21.sinv L = L⁻¹ := rfl

abbrev ρd (d : ℕ) : Matrix (Wire d) (Wire d) ℂ := ((d : ℂ)⁻¹) • 1

lemma oD_LW (M : Matrix (Four d) (Four d) ℂ) (L W U : SU d) :
    outcomeDensity (covarianceAction L W M) U (ρd d) = outcomeDensity M (L⁻¹ * U * W) (ρd d) := by
  have e : covarianceAction L W M = covariantDensity (covarianceAction 1 W M) L := by
    rw [covariantDensity, ← cA_mul, mul_one, one_mul]
  rw [e, X7PS.oD_eq, X7PS.oD_eq]
  simp_rw [X7PS.Lk_cov]
  rw [← X7PS.oD_eq, ← X7PS.oD_eq, X7AF.oD_T2, X7AF.oD_T2, T2_cA, sinv_eq]

end X7CR

-- ===== p21c/R7 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

def nV (V U : SU d) : ℝ := Complex.normSq ((unitaryMatrix V)ᴴ * unitaryMatrix U).trace

def gR (H : HaarLaw d) (V : SU d) (M : Matrix (Four d) (Four d) ℂ) : ℝ :=
  ∫ U, outcomeDensity M U (ρd d) * nV V U / (d : ℝ)^2 ∂H.law

lemma T2_cont (M : Matrix (Four d) (Four d) ℂ) : Continuous fun U : SU d => X7AF.T2 M U := by
  unfold X7AF.T2 linkedChoi
  have hv := X7P21.val_cont (d := d)
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun e _ => ?_
  refine continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun b' _ => continuous_finset_sum _ fun c' _ => ?_
  exact ((hv.matrix_elem b c).mul continuous_const).mul (Complex.continuous_conj.comp (hv.matrix_elem b' c'))

lemma oD_cont (M : Matrix (Four d) (Four d) ℂ) : Continuous fun U : SU d => outcomeDensity M U (ρd d) := by
  simp_rw [X7AF.oD_T2]
  exact Complex.continuous_re.comp (continuous_const.mul (T2_cont M))

lemma nV_cont (V : SU d) : Continuous fun U : SU d => nV V U := by
  unfold nV
  exact Complex.continuous_normSq.comp ((continuous_const.matrix_mul X7P21.val_cont).matrix_trace)

lemma gR_int (H : HaarLaw d) (V : SU d) (M : Matrix (Four d) (Four d) ℂ) :
    Integrable (fun U => outcomeDensity M U (ρd d) * nV V U / (d : ℝ)^2) H.law :=
  X7P21.integrable_of_cont H (((oD_cont M).mul (nV_cont V)).div_const _)

lemma oD_add (M N : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    outcomeDensity (M + N) U (ρd d) = outcomeDensity M U (ρd d) + outcomeDensity N U (ρd d) := by
  simp only [X7AF.oD_T2, ← X7AF.T2L_apply, map_add, mul_add, Complex.add_re]

lemma oD_smul (r : ℝ) (M : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    outcomeDensity (r • M) U (ρd d) = r * outcomeDensity M U (ρd d) := by
  simp only [X7AF.oD_T2, ← X7AF.T2L_apply]
  rw [show (r • M) = (r : ℂ) • M from (RCLike.real_smul_eq_coe_smul (K := ℂ) r M), map_smul, smul_eq_mul,
    mul_left_comm, Complex.re_ofReal_mul]

def gRL (H : HaarLaw d) (V : SU d) : Matrix (Four d) (Four d) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := gR H V
      map_add' := fun M N => by
        unfold gR
        simp only [oD_add, add_mul, add_div]
        exact integral_add (gR_int H V M) (gR_int H V N)
      map_smul' := fun r M => by
        unfold gR
        simp only [oD_smul, RingHom.id_apply, smul_eq_mul, mul_assoc, mul_div_assoc]
        rw [integral_const_mul] }

lemma gRL_apply (H : HaarLaw d) (V : SU d) (M : Matrix (Four d) (Four d) ℂ) : gRL H V M = gR H V M := rfl

lemma int_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : HaarLaw d) (V : SU d)
    (f : SU d → E) : ∫ U, f (U * V) ∂H.law = ∫ U, f U ∂H.law :=
  (MeasurePreserving.integral_comp ⟨(continuous_id.mul continuous_const).measurable, H.right_invariant V⟩
    (Homeomorph.mulRight V).measurableEmbedding f)

lemma gR_cov (H : HaarLaw d) (V L W : SU d) (M : Matrix (Four d) (Four d) ℂ) :
    gR H V (covarianceAction L W M) = gR H (L⁻¹ * V * W) M := by
  unfold gR
  simp_rw [oD_LW]
  rw [← int_left H L, ← int_right H W⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only
  have e1 : L⁻¹ * (L * (U * W⁻¹)) * W = U := by group
  rw [e1]
  have hn : nV V (L * (U * W⁻¹)) = nV (L⁻¹ * V * W) U := by
    unfold nV
    have hL : unitaryMatrix L⁻¹ = (unitaryMatrix L)ᴴ := rfl
    have hW : unitaryMatrix W⁻¹ = (unitaryMatrix W)ᴴ := rfl
    rw [um_mul, um_mul, um_mul, um_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hL, hW,
      Matrix.conjTranspose_conjTranspose]
    congr 1
    calc ((unitaryMatrix V)ᴴ * (unitaryMatrix L * (unitaryMatrix U * (unitaryMatrix W)ᴴ))).trace
        = ((unitaryMatrix V)ᴴ * (unitaryMatrix L * unitaryMatrix U) * (unitaryMatrix W)ᴴ).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((unitaryMatrix W)ᴴ * ((unitaryMatrix V)ᴴ * (unitaryMatrix L * unitaryMatrix U))).trace := by
          rw [Matrix.trace_mul_comm]
      _ = ((unitaryMatrix W)ᴴ * ((unitaryMatrix V)ᴴ * unitaryMatrix L) * unitaryMatrix U).trace := by
          simp only [Matrix.mul_assoc]
  rw [hn]

end X7CR

-- ===== p21c/R8 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

lemma gain_R (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ)
    (hgain : Integrable (fun t : SU d × SU d => gainKernel (R t.2) t.1 t.2) (H.law.prod H.law)) :
    gain H R = ∫ V, gR H V (R V) ∂H.law := by
  haveI := H.probability
  rw [gain, integral_prod_symm _ hgain]
  rfl

lemma gain_cD (H : HaarLaw d) (X : Matrix (Four d) (Four d) ℂ)
    (hgain : Integrable (fun t : SU d × SU d => gainKernel (covariantDensity X t.2) t.1 t.2) (H.law.prod H.law)) :
    gain H (covariantDensity X) = gR H 1 X := by
  haveI := H.probability
  rw [gain_R H _ hgain]
  have : ∀ V : SU d, gR H V (covariantDensity X V) = gR H 1 X := by
    intro V
    rw [covariantDensity, gR_cov]
    congr 1
    group
  simp only [this, integral_const, probReal_univ, one_smul]

theorem gain_X (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (hR : Integrable R H.law)
    (hgain : Integrable (fun t : SU d × SU d => gainKernel (R t.2) t.1 t.2) (H.law.prod H.law))
    (hgainX : Integrable (fun t : SU d × SU d => gainKernel (covariantDensity (twirl H R 1) t.2) t.1 t.2)
      (H.law.prod H.law)) :
    gain H (covariantDensity (twirl H R 1)) = gain H R := by
  haveI := H.probability
  rw [gain_cD H _ hgainX, X_eq H R hR, ← gRL_apply, ← (gRL H 1).integral_comp_comm
    (X7P21.integrable_of_cont H (hcL _))]
  simp only [gRL_apply]
  have h1 : ∀ L : SU d, gR H 1 (covarianceAction L L (Yr H R)) = gR H 1 (Yr H R) := by
    intro L
    rw [gR_cov]
    congr 1
    group
  simp only [h1, integral_const, probReal_univ, one_smul]
  rw [Yr, ← gRL_apply, ← (gRL H 1).integral_comp_comm
    (cA_integrable H R hR (fun _ => 1) (fun U => U) continuous_const continuous_id)]
  simp only [gRL_apply, gR_cov, inv_one, one_mul]
  rw [gain_R H R hgain]

end X7CR

-- ===== p21c/R9 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

def Seeds (d : ℕ) : Set (Matrix (Four d) (Four d) ℂ) :=
  {X | X.PosSemidef ∧ SeedCommutes X ∧ X.trace = (d : ℂ)^2}

lemma cnonneg_closed : IsClosed {z : ℂ | 0 ≤ z} := by
  have : {z : ℂ | 0 ≤ z} = {z | 0 ≤ z.re} ∩ {z | z.im = 0} := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.nonneg_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  rw [this]
  exact (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_eq Complex.continuous_im continuous_const)

lemma psd_closed : IsClosed {X : Matrix (Four d) (Four d) ℂ | X.PosSemidef} := by
  have : {X : Matrix (Four d) (Four d) ℂ | X.PosSemidef} =
      {X | Xᴴ = X} ∩ ⋂ v : Four d → ℂ, {X | 0 ≤ star v ⬝ᵥ (X *ᵥ v)} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter (isClosed_iInter fun v => ?_)
  exact cnonneg_closed.preimage (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

lemma seeds_closed : IsClosed (Seeds d) := by
  have : Seeds d = {X | X.PosSemidef} ∩ ((⋂ V : SU d, {X | X * representation V V = representation V V * X}) ∩
      {X | X.trace = (d : ℂ)^2}) := by
    ext X; simp [Seeds, SeedCommutes]
  rw [this]
  refine psd_closed.inter ((isClosed_iInter fun V => ?_).inter ?_)
  · exact isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id)
  · exact isClosed_eq continuous_id.matrix_trace continuous_const

lemma diag_le (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef) (ht : X.trace = (d : ℂ)^2) (k : Four d) :
    (X k k).re ≤ (d : ℝ)^2 := by
  have h1 : ((d : ℂ)^2).re = (d : ℝ)^2 := by norm_cast
  rw [← h1, ← ht, Matrix.trace, Complex.re_sum]
  exact Finset.single_le_sum (f := fun i => (X.diag i).re)
    (fun i _ => (Complex.nonneg_iff.mp (hX.diag_nonneg (i := i))).1) (Finset.mem_univ k)

lemma entry_le (X : Matrix (Four d) (Four d) ℂ) (hX : X.PosSemidef) (ht : X.trace = (d : ℂ)^2) (i j : Four d) :
    ‖X i j‖ ≤ (d : ℝ)^2 := by
  have hs := hX.submatrix ![i, j]
  have hdet := hs.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have hji : X j i = conj (X i j) := by
    have := congrFun (congrFun hX.isHermitian j) i
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]; rfl
  have hii := Complex.nonneg_iff.mp (hX.diag_nonneg (i := i))
  have hjj := Complex.nonneg_iff.mp (hX.diag_nonneg (i := j))
  rw [hji, Complex.mul_conj, Complex.nonneg_iff] at hdet
  have hre : (X i i * X j j).re = (X i i).re * (X j j).re := by
    rw [Complex.mul_re, ← hii.2, ← hjj.2]; ring
  have h1 := hdet.1
  rw [Complex.sub_re, hre, Complex.ofReal_re] at h1
  have hn : Complex.normSq (X i j) ≤ ((d : ℝ)^2)^2 := by
    have a := diag_le X hX ht i
    have b := diag_le X hX ht j
    nlinarith
  rw [Complex.normSq_eq_norm_sq] at hn
  have : (0 : ℝ) ≤ (d : ℝ)^2 := by positivity
  nlinarith [norm_nonneg (X i j)]

lemma seeds_compact : IsCompact (Seeds d) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Four d =>
      Set.pi Set.univ fun _ : Four d => Metric.closedBall (0 : ℂ) ((d : ℝ)^2)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset seeds_closed ?_
  intro X hX
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => entry_le X hX.1 hX.2.2 i j

lemma seeds_nonempty (hd : 0 < d) : (Seeds d).Nonempty := by
  refine ⟨(((d : ℝ)^2)⁻¹ : ℝ) • (1 : Matrix (Four d) (Four d) ℂ), ?_, ?_, ?_⟩
  · exact Matrix.PosSemidef.one.smul (by positivity)
  · intro V
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_prod, Fintype.card_fin]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [Complex.real_smul]
    push_cast
    field_simp

end X7CR

-- ===== p21c/R10 =====

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7CR
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

variable {d : ℕ}

theorem part1 (hd : 2 ≤ d) (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) (h0 : 0 < d)
    (hR : IsHaarCombInstrument H h0 R) :
    ∃ X : Matrix (Four d) (Four d) ℂ,
        X.PosSemidef ∧ SeedCommutes X ∧ X.trace = (d : ℂ)^2 ∧
        IsHaarCombInstrument H h0 (covariantDensity X) ∧ Continuous (covariantDensity X) ∧
        channelScore H (covariantDensity X) = channelScore H R ∧
        gain H (covariantDensity X) = gain H R ∧
        (∀ V, covariantDensity X V = twirl H R V) ∧
        (∀ V L W : SU d, covariantDensity X (L * V * W⁻¹) =
          covarianceAction L W (covariantDensity X V)) := by
  obtain ⟨_, hpsd, hint, _, hcomb, hfid, hgain, _⟩ := hR
  have hXp := X_psd H R hint hpsd
  have hXc := X_comm H R hint
  have hXt := X_trace H R hint hcomb
  have hinst := X7PS.inst H hd _ hXp hXc hXt h0
  exact ⟨twirl H R 1, hXp, hXc, hXt, hinst, X7P21.cD_cont _, score_X H hd R hint hfid,
    gain_X H R hint hgain hinst.2.2.2.2.2.2.1, fun V => (twirl_cov H R hint V).symm, X_cov H R hint⟩

theorem part2 (hd : 2 ≤ d) (H : HaarLaw d) (h0 : 0 < d) (p : ℝ) :
    ∃ X : Matrix (Four d) (Four d) ℂ,
      X.PosSemidef ∧ SeedCommutes X ∧
      IsHaarCombInstrument H h0 (covariantDensity X) ∧
      ∀ R : SU d → Matrix (Four d) (Four d) ℂ, IsHaarCombInstrument H h0 R →
        p * gain H R + (1-p) * channelScore H R ≤
          p * gain H (covariantDensity X) + (1-p) * channelScore H (covariantDensity X) := by
  set f : Matrix (Four d) (Four d) ℂ → ℝ := fun X =>
    p * ((lambdaG d * X).trace).re + (1 - p) * ((lambdaF d * X).trace).re with hf
  have hfc : Continuous f := by
    rw [hf]
    exact (continuous_const.mul (Complex.continuous_re.comp (continuous_const.matrix_mul continuous_id).matrix_trace)).add
      (continuous_const.mul (Complex.continuous_re.comp (continuous_const.matrix_mul continuous_id).matrix_trace))
  obtain ⟨X, hX, hmax⟩ := seeds_compact.exists_isMaxOn (seeds_nonempty h0) hfc.continuousOn
  have hval : ∀ Y ∈ Seeds d, p * gain H (covariantDensity Y) + (1 - p) * channelScore H (covariantDensity Y) = f Y := by
    intro Y hY
    rw [hf, X7PS.gain_val H hd Y hY.2.1 hY.2.2, X7PS.score H hd]
  refine ⟨X, hX.1, hX.2.1, X7PS.inst H hd X hX.1 hX.2.1 hX.2.2 h0, fun R hR => ?_⟩
  obtain ⟨Y, hYp, hYc, hYt, _, _, hF, hG, _, _⟩ := part1 hd H R h0 hR
  rw [← hF, ← hG, hval Y ⟨hYp, hYc, hYt⟩, hval X hX]
  exact hmax ⟨hYp, hYc, hYt⟩

end X7CR

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

open QAlgorithms.Papers.Independent.Claimed50.P21 in
theorem solution (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    (∀ R : SU d → Matrix (Four d) (Four d) ℂ, IsHaarCombInstrument H (by omega) R →
      ∃ X : Matrix (Four d) (Four d) ℂ,
        X.PosSemidef ∧ SeedCommutes X ∧ X.trace = (d : ℂ)^2 ∧
        IsHaarCombInstrument H (by omega) (covariantDensity X) ∧ Continuous (covariantDensity X) ∧
        channelScore H (covariantDensity X) = channelScore H R ∧
        gain H (covariantDensity X) = gain H R ∧
        (∀ V, covariantDensity X V = twirl H R V) ∧
        (∀ V L W : SU d, covariantDensity X (L * V * W⁻¹) =
          covarianceAction L W (covariantDensity X V))) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∃ X : Matrix (Four d) (Four d) ℂ,
      X.PosSemidef ∧ SeedCommutes X ∧
      IsHaarCombInstrument H (by omega) (covariantDensity X) ∧
      ∀ R : SU d → Matrix (Four d) (Four d) ℂ, IsHaarCombInstrument H (by omega) R →
        p * gain H R + (1-p) * channelScore H R ≤
          p * gain H (covariantDensity X) + (1-p) * channelScore H (covariantDensity X)) :=
  ⟨fun R hR => X7CR.part1 hd H R _ hR, fun p _ _ => X7CR.part2 hd H _ p⟩

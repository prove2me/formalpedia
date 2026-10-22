-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P20.catRedistribution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:53:55.343571+00:00
-- url     : https://prove2.me/submissions/6b5e4084-6b4b-4b3f-a766-858c9dfbc894

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev g74d_Src := RedistributionSource Bool Bool Bool Bool

def g74d_c (z : Bool) : g74d_Src := (z, (z, (z, z)))

lemma g74d_cat_apply (x : g74d_Src) :
    catState x = if x = g74d_c x.1 then ((Real.sqrt 2)⁻¹ : ℂ) else 0 := by
  obtain ⟨r, a, c, b⟩ := x
  cases r <;> cases a <;> cases c <;> cases b <;> simp [catState, g74d_c]

lemma g74d_sum_cat (F : g74d_Src → ℂ) :
    ∑ x, catState x * F x = ((Real.sqrt 2)⁻¹ : ℂ) * F (g74d_c false) +
      ((Real.sqrt 2)⁻¹ : ℂ) * F (g74d_c true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [catState, g74d_c]; ring

lemma g74d_sum_cat' (F : g74d_Src → ℂ) :
    ∑ x, conj (catState x) * F x = ((Real.sqrt 2)⁻¹ : ℂ) * F (g74d_c false) +
      ((Real.sqrt 2)⁻¹ : ℂ) * F (g74d_c true) := by
  have h : conj ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
    rw [← Complex.ofReal_inv, Complex.conj_ofReal]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [catState, g74d_c, h]; ring

lemma g74d_ss : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma g74d_state : IsState catState := by
  unfold IsState
  rw [EuclideanSpace.norm_eq]
  have : ∑ x, ‖catState x‖ ^ 2 = 1 := by
    have h1 : ∀ x, (‖catState x‖ ^ 2 : ℝ) = (catState x * conj (catState x)).re := by
      intro x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
    simp only [h1]
    rw [← Complex.re_sum]
    have := g74d_sum_cat (fun x => conj (catState x))
    rw [this]
    simp only [g74d_cat_apply, g74d_c, if_true]
    have h : conj ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
      rw [← Complex.ofReal_inv, Complex.conj_ofReal]
    rw [h, g74d_ss]; norm_num
  rw [this, Real.sqrt_one]

lemma g74d_marg {K F : Type*} (keep : g74d_Src → K) (forget : g74d_Src → F)
    (hf : forget (g74d_c false) ≠ forget (g74d_c true)) :
    redistributionMarginal (pureDensity catState) keep forget = fun a b =>
      (1/2 : ℂ) * ((if keep (g74d_c false) = a ∧ keep (g74d_c false) = b then 1 else 0) +
        (if keep (g74d_c true) = a ∧ keep (g74d_c true) = b then 1 else 0)) := by
  funext a b
  unfold redistributionMarginal
  have e : ∀ x y : g74d_Src, (if keep x = a ∧ keep y = b ∧ forget x = forget y then
      pureDensity catState x y else 0) = catState x * (conj (catState y) *
      (if keep x = a ∧ keep y = b ∧ forget x = forget y then 1 else 0)) := by
    intro x y; simp only [pureDensity, Matrix.of_apply]; split_ifs <;> ring
  simp only [e]
  simp only [← Finset.mul_sum]
  rw [g74d_sum_cat]
  simp only [g74d_sum_cat']
  have hf' := hf.symm
  simp only [hf, hf', and_false, if_false, and_true, mul_zero, add_zero, zero_add]
  rw [← g74d_ss]; ring

lemma g74d_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g74d_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g74d_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g74d_diag_herm d
  rw [g74d_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma g74d_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g74d_trace_cfc_diag]
  simp

lemma g74d_vn_two {K : Type*} [Fintype K] [DecidableEq K] (k0 k1 : K) (h : k0 ≠ k1) :
    vnEntropy (fun a b : K => (1/2 : ℂ) * ((if k0 = a ∧ k0 = b then 1 else 0) +
        (if k1 = a ∧ k1 = b then 1 else 0))) = 1 := by
  have e : (fun a b : K => (1/2 : ℂ) * ((if k0 = a ∧ k0 = b then 1 else 0) +
        (if k1 = a ∧ k1 = b then 1 else 0))) = Matrix.diagonal (fun i =>
        (((if i = k0 then 1/2 else 0) + (if i = k1 then 1/2 else 0) : ℝ) : ℂ)) := by
    funext a b
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; by_cases h0 : a = k0
      · subst h0; simp [h, Ne.symm h]
      · by_cases h1 : a = k1
        · subst h1; simp [Ne.symm h, h]
        · simp [h0, h1, Ne.symm h0, Ne.symm h1]
    · rw [if_neg hab]
      have h2 : ¬ (k0 = a ∧ k0 = b) := fun ⟨u, v⟩ => hab (u.symm.trans v)
      have h3 : ¬ (k1 = a ∧ k1 = b) := fun ⟨u, v⟩ => hab (u.symm.trans v)
      rw [if_neg h2, if_neg h3]; simp
  rw [e, g74d_vn_diag]
  have p : ∀ i : K, ((if i = k0 then 1/2 else 0) + (if i = k1 then 1/2 else 0) : ℝ) *
      Real.logb 2 ((if i = k0 then 1/2 else 0) + (if i = k1 then 1/2 else 0)) =
      (if i = k0 then (1/2 : ℝ) * Real.logb 2 (1/2) else 0) +
      (if i = k1 then (1/2 : ℝ) * Real.logb 2 (1/2) else 0) := by
    intro i
    by_cases h0 : i = k0
    · subst h0; simp [h]
    · by_cases h1 : i = k1
      · subst h1; simp [h0]
      · simp [h0, h1]
  simp only [p, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have : Real.logb 2 (1/2) = -1 := by
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  rw [this]; norm_num

lemma g74d_ent {K F : Type*} [Fintype K] (keep : g74d_Src → K) (forget : g74d_Src → F)
    (hf : forget (g74d_c false) ≠ forget (g74d_c true))
    (hk : keep (g74d_c false) ≠ keep (g74d_c true)) :
    subsystemEntropy (pureDensity catState) keep forget = 1 := by
  unfold subsystemEntropy
  rw [g74d_marg keep forget hf]
  exact g74d_vn_two _ _ hk

lemma g74d_costs : quantumCost catState = 0 ∧ redistributionEntanglementRate catState = 0 := by
  unfold quantumCost redistributionEntanglementRate
  rw [g74d_ent, g74d_ent, g74d_ent, g74d_ent, g74d_ent, g74d_ent]
  all_goals simp [g74d_c]

lemma g74d_isChannel_kraus {K ι κ : Type*} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (h : ∑ j, (E j)ᴴ * E j = 1) : IsChannel (krausApply E) := by
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (e.symm j), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← h]
    exact Equiv.sum_comp e.symm (fun j => (E j)ᴴ * E j)
  · intro ρ
    unfold krausApply
    exact (Equiv.sum_comp e.symm (fun j => E j * ρ * (E j)ᴴ)).symm

lemma g74d_conj_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix κ ι ℂ) (x x' : ι)
    (o o' : κ) : (A * Matrix.single x x' (1 : ℂ) * Bᴴ) o o' = A o x * conj (B o' x') := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, Finset.sum_ite_eq]

section g74dsec
variable (n : ℕ)

abbrev g74d_CB := Fin n → Bool

def g74d_xor (x : (g74d_CB n × g74d_CB n) × Qubits 0) : g74d_CB n := fun i => x.1.1 i != x.1.2 i

def g74d_EK (w : g74d_CB n) :
    Matrix ((g74d_CB n × Qubits 0) × Qubits 0) ((g74d_CB n × g74d_CB n) × Qubits 0) ℂ :=
  fun o x => if o.1.1 = x.1.1 ∧ w = g74d_xor n x then 1 else 0

def g74d_DV :
    Matrix ((g74d_CB n × g74d_CB n) × Qubits 0) (Qubits 0 × (g74d_CB n × Qubits 0)) ℂ :=
  fun o y => if o.1.1 = y.2.1 ∧ o.1.2 = y.2.1 then 1 else 0

lemma g74d_xor_inj (x x' : (g74d_CB n × g74d_CB n) × Qubits 0) (h1 : x.1.1 = x'.1.1)
    (h2 : g74d_xor n x = g74d_xor n x') : x = x' := by
  obtain ⟨⟨a, c⟩, e⟩ := x
  obtain ⟨⟨a', c'⟩, e'⟩ := x'
  simp only at h1
  subst h1
  have : c = c' := by
    funext i
    have := congrFun h2 i
    simp only [g74d_xor] at this
    cases ha : a i <;> cases hc : c i <;> cases hc' : c' i <;> simp_all
  subst this
  rw [Subsingleton.elim e e']

lemma g74d_ite_prod (P Q : Prop) [Decidable P] [Decidable Q] :
    conj (if P then (1 : ℂ) else 0) * (if Q then (1 : ℂ) else 0) = if P ∧ Q then 1 else 0 := by
  by_cases h1 : P <;> by_cases h2 : Q
  · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]; simp
  · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; simp
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]; simp
  · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1)]; simp

lemma g74d_EK_term (w : g74d_CB n) (o : (g74d_CB n × Qubits 0) × Qubits 0)
    (x x' : (g74d_CB n × g74d_CB n) × Qubits 0) :
    conj (g74d_EK n w o x) * g74d_EK n w o x' =
      if (o.1.1 = x.1.1 ∧ w = g74d_xor n x) ∧ (o.1.1 = x'.1.1 ∧ w = g74d_xor n x') then 1 else 0 := by
  show conj (if o.1.1 = x.1.1 ∧ w = g74d_xor n x then (1 : ℂ) else 0) *
    (if o.1.1 = x'.1.1 ∧ w = g74d_xor n x' then (1 : ℂ) else 0) = _
  exact g74d_ite_prod _ _

lemma g74d_EK_kraus [DecidableEq ((g74d_CB n × g74d_CB n) × Qubits 0)] : ∑ w, (g74d_EK n w)ᴴ * g74d_EK n w = 1 := by
  ext x x'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, g74d_EK_term]
  rw [Matrix.one_apply]
  by_cases hx : x = x'
  · subst hx
    simp only [and_self, if_true]
    rw [Fintype.sum_eq_single (g74d_xor n x)]
    · rw [Fintype.sum_eq_single ((x.1.1, default), default)]
      · simp
      · intro o ho
        rw [if_neg]
        rintro ⟨h1, -⟩
        apply ho
        obtain ⟨⟨u, e⟩, e2⟩ := o
        simp only at h1
        subst h1
        rw [Subsingleton.elim e default, Subsingleton.elim e2 default]
    · intro w hw
      apply Finset.sum_eq_zero
      intro o _
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact hw h2
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro w _
    apply Finset.sum_eq_zero
    intro o _
    rw [if_neg]
    rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact hx (g74d_xor_inj n x x' (h1.symm.trans h3) (h2.symm.trans h4))

lemma g74d_DV_iso [DecidableEq (Qubits 0 × (g74d_CB n × Qubits 0))] : (g74d_DV n)ᴴ * g74d_DV n = 1 := by
  ext y y'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, g74d_DV]
  rw [Matrix.one_apply]
  have t : ∀ o : (g74d_CB n × g74d_CB n) × Qubits 0,
      conj (if o.1.1 = y.2.1 ∧ o.1.2 = y.2.1 then (1 : ℂ) else 0) *
        (if o.1.1 = y'.2.1 ∧ o.1.2 = y'.2.1 then 1 else 0) =
      if (o.1.1 = y.2.1 ∧ o.1.2 = y.2.1) ∧ (o.1.1 = y'.2.1 ∧ o.1.2 = y'.2.1) then 1 else 0 := by
    intro o; exact g74d_ite_prod _ _
  simp only [t]
  by_cases hy : y = y'
  · subst hy
    simp only [and_self, if_true]
    rw [Fintype.sum_eq_single ((y.2.1, y.2.1), default)]
    · simp
    · intro o ho
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply ho
      obtain ⟨⟨u, v⟩, e⟩ := o
      simp only at h1 h2
      subst h1 h2
      rw [Subsingleton.elim e default]
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro o _
    rw [if_neg]
    rintro ⟨⟨h1, -⟩, ⟨h3, -⟩⟩
    apply hy
    obtain ⟨e, ⟨b, e'⟩⟩ := y
    obtain ⟨f, ⟨b', f'⟩⟩ := y'
    simp only at h1 h3
    rw [Subsingleton.elim e f, Subsingleton.elim e' f', ← h1, h3]

lemma g74d_ite_prod' (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℂ) else 0) * conj (if Q then (1 : ℂ) else 0) = if P ∧ Q then 1 else 0 := by
  rw [mul_comm, g74d_ite_prod]; exact if_congr and_comm rfl rfl

def g74d_enc : Superop ((g74d_CB n × g74d_CB n) × Qubits 0) ((g74d_CB n × Qubits 0) × Qubits 0) :=
  krausApply (g74d_EK n)

def g74d_dec : Superop (Qubits 0 × (g74d_CB n × Qubits 0)) ((g74d_CB n × g74d_CB n) × Qubits 0) :=
  conjSuperop (g74d_DV n)

lemma g74d_enc_single [DecidableEq ((g74d_CB n × g74d_CB n) × Qubits 0)] (x x' : (g74d_CB n × g74d_CB n) × Qubits 0)
    (o o' : (g74d_CB n × Qubits 0) × Qubits 0) :
    g74d_enc n (Matrix.single x x' 1) o o' =
      if o.1.1 = x.1.1 ∧ o'.1.1 = x'.1.1 ∧ g74d_xor n x = g74d_xor n x' then 1 else 0 := by
  unfold g74d_enc krausApply
  rw [Matrix.sum_apply]
  simp only [g74d_conj_single]
  have t : ∀ w, g74d_EK n w o x * conj (g74d_EK n w o' x') =
      if (o.1.1 = x.1.1 ∧ w = g74d_xor n x) ∧ (o'.1.1 = x'.1.1 ∧ w = g74d_xor n x') then 1 else 0 :=
    fun w => g74d_ite_prod' _ _
  simp only [t]
  rw [Fintype.sum_eq_single (g74d_xor n x)]
  · by_cases h1 : o.1.1 = x.1.1 <;> by_cases h2 : o'.1.1 = x'.1.1 <;>
      by_cases h3 : g74d_xor n x = g74d_xor n x' <;> simp [h1, h2, h3, eq_comm]
  · intro w hw
    rw [if_neg]
    rintro ⟨⟨-, h⟩, -⟩
    exact hw h

lemma g74d_dec_single [DecidableEq (Qubits 0 × (g74d_CB n × Qubits 0))] (y y' : Qubits 0 × (g74d_CB n × Qubits 0))
    (u u' : (g74d_CB n × g74d_CB n) × Qubits 0) :
    g74d_dec n (Matrix.single y y' 1) u u' =
      if (u.1.1 = y.2.1 ∧ u.1.2 = y.2.1) ∧ (u'.1.1 = y'.2.1 ∧ u'.1.2 = y'.2.1) then 1 else 0 := by
  unfold g74d_dec conjSuperop
  rw [g74d_conj_single]
  exact g74d_ite_prod' _ _

lemma g74d_sA (r a c b : Fin n → Bool) :
    sourceAmplitude catState n r a c b =
      if a = r ∧ c = r ∧ b = r then ((Real.sqrt 2)⁻¹ : ℂ) ^ n else 0 := by
  unfold sourceAmplitude tensorPow
  simp only [PiLp.toLp_apply, WithLp.ofLp_toLp]
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := h
    subst h1 h2 h3
    rw [← Fin.prod_const]
    apply Finset.prod_congr rfl
    intro i _
    simp [catState]
  · apply Finset.prod_eq_zero_iff.mpr
    by_contra hne
    push_neg at hne
    apply h
    have key : ∀ i, a i = r i ∧ c i = r i ∧ b i = r i := by
      intro i
      have := hne i (Finset.mem_univ _)
      simp only [catState, PiLp.toLp_apply, WithLp.ofLp_toLp, ne_eq, ite_eq_right_iff,
        not_forall] at this
      obtain ⟨⟨h1, h2, h3⟩, -⟩ := this
      exact ⟨h1.symm, (h1.trans h2).symm, (h1.trans (h2.trans h3)).symm⟩
    exact ⟨funext fun i => (key i).1, funext fun i => (key i).2.1, funext fun i => (key i).2.2⟩

def g74d_code : TransferCode Bool Bool Bool n where
  q := 0
  k := 0
  l := 0
  encoder := g74d_enc n
  decoder := g74d_dec n
  encoder_channel := by convert g74d_isChannel_kraus (g74d_EK n) (by convert g74d_EK_kraus n) <;> rfl
  decoder_channel := ⟨1, fun _ => g74d_DV n, by
    unfold IsKrausFamily; rw [Fin.sum_univ_one]; convert g74d_DV_iso n, by
    intro ρ; simp [krausApply, g74d_dec, conjSuperop]⟩

lemma g74d_me0 (z : Qubits 0 × Qubits 0) : maxEntangled 0 z = 1 := by
  simp [maxEntangled, Subsingleton.elim z.1 z.2]

lemma g74d_v (r : Fin n → Bool) (x : (g74d_CB n × g74d_CB n) × Qubits 0)
    (y : g74d_CB n × Qubits 0) :
    sourceAmplitude catState n r x.1.1 x.1.2 y.1 =
      if x = ((r, r), default) ∧ y = (r, default) then ((Real.sqrt 2)⁻¹ : ℂ) ^ n else 0 := by
  rw [g74d_sA]
  congr 1
  apply propext
  obtain ⟨⟨a, c⟩, e⟩ := x
  obtain ⟨b, e'⟩ := y
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨⟨h1, h2⟩, Subsingleton.elim _ _⟩, h3, Subsingleton.elim _ _⟩
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3, -⟩
    exact ⟨h1, h2, h3⟩

lemma g74d_xor_diag (r : g74d_CB n) (e : Qubits 0) : g74d_xor n ((r, r), e) = fun _ => false := by
  funext i; simp [g74d_xor]

lemma g74d_out' : idTensorSuperop (R := Copies Bool n) (forwardApply (g74d_enc n) (g74d_dec n))
    (pureDensity (WithLp.toLp 2 fun p : Copies Bool n × (((Copies Bool n × Copies Bool n) × Qubits 0) ×
      (Copies Bool n × Qubits 0)) => sourceAmplitude catState n p.1 p.2.1.1.1 p.2.1.1.2 p.2.2.1 *
        maxEntangled 0 (p.2.1.2, p.2.2.2))) =
    pureDensity (WithLp.toLp 2 fun p : Copies Bool n × ((Copies Bool n × Qubits 0) ×
      ((Copies Bool n × Copies Bool n) × Qubits 0)) =>
        sourceAmplitude catState n p.1 p.2.1.1 p.2.2.1.1 p.2.2.1.2 * maxEntangled 0 (p.2.1.2, p.2.2.2)) := by
  funext p p'
  simp only [idTensorSuperop, forwardApply, pureDensity, Matrix.of_apply, PiLp.toLp_apply,
    g74d_me0, mul_one]
  simp only [g74d_enc_single, g74d_dec_single, g74d_v]
  simp only [g74d_sA]
  simp only [ite_and, apply_ite (starRingEnd ℂ), map_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_unique]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, g74d_xor_diag, mul_one]
  rw [Fintype.sum_eq_single ((p'.1, p'.1), default) (by
    intro x hx; simp only [hx, if_false, ite_self, Finset.sum_const_zero])]
  rw [Fintype.sum_eq_single (p'.1, default) (by
    intro x hx; simp only [hx, if_false, ite_self])]
  simp only [g74d_xor_diag, if_true]
  by_cases h1 : p.2.1.1 = p.1 <;> by_cases h2 : p.2.2.1.1 = p.1 <;> by_cases h3 : p.2.2.1.2 = p.1 <;>
    by_cases h4 : p'.2.1.1 = p'.1 <;> by_cases h5 : p'.2.2.1.1 = p'.1 <;>
    by_cases h6 : p'.2.2.1.2 = p'.1 <;> simp only [h1, h2, h3, h4, h5, h6, if_true, if_false]

lemma g74d_out :
    (g74d_code n).redistributionOutputDensity catState =
      (g74d_code n).redistributionTargetDensity catState := g74d_out' n

end g74dsec

lemma g74d_alice_kraus [DecidableEq (Bool × Bool)] : ∑ w, (catAliceKraus w)ᴴ * catAliceKraus w = 1 := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  rw [Matrix.one_apply]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool,
    catAliceKraus]
  cases a <;> cases c <;> cases a' <;> cases c' <;> simp

lemma g74d_alice_ch : IsChannel catAlice := by
  unfold catAlice
  exact g74d_isChannel_kraus _ (g74d_alice_kraus)

lemma g74d_bob_ch : IsChannel catBob := by
  refine ⟨1, fun _ => catBobIsometry, ?_, ?_⟩
  · unfold IsKrausFamily
    rw [Fin.sum_univ_one]
    ext a b
    rw [Matrix.one_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      catBobIsometry]
    cases a <;> cases b <;> simp
  · intro ρ; simp [krausApply, catBob, conjSuperop]

lemma g74d_alice_single [DecidableEq (Bool × Bool)] (x x' : Bool × Bool) (a a' : Bool) :
    catAlice (Matrix.single x x' 1) a a' =
      if a = x.1 ∧ a' = x'.1 ∧ (x.1 != x.2) = (x'.1 != x'.2) then 1 else 0 := by
  unfold catAlice krausApply
  rw [Matrix.sum_apply]
  simp only [g74d_conj_single, Fintype.sum_bool, catAliceKraus]
  obtain ⟨u, v⟩ := x
  obtain ⟨u', v'⟩ := x'
  cases u <;> cases v <;> cases u' <;> cases v' <;> cases a <;> cases a' <;> simp

lemma g74d_bob_single [DecidableEq Bool] (y y' : Bool) (u u' : Bool × Bool) :
    catBob (Matrix.single y y' 1) u u' = if u = (y, y) ∧ u' = (y', y') then 1 else 0 := by
  unfold catBob conjSuperop
  rw [g74d_conj_single]
  unfold catBobIsometry; convert g74d_ite_prod' (u = (y, y)) (u' = (y', y'))

lemma g74d_in (r : Bool) (x : Bool × Bool) (b : Bool) :
    catState (r, (x.1, (x.2, b))) = if x = (r, r) ∧ b = r then ((Real.sqrt 2)⁻¹ : ℂ) else 0 := by
  obtain ⟨u, v⟩ := x
  cases r <;> cases u <;> cases v <;> cases b <;> simp [catState]

lemma g74d_oneshot : idTensorSuperop (localProduct catAlice catBob) catInput = pureDensity catState := by
  funext p p'
  simp only [idTensorSuperop, localProduct, catInput, pureDensity, Matrix.of_apply, PiLp.toLp_apply]
  simp only [g74d_alice_single, g74d_bob_single, g74d_in]
  simp only [ite_and, apply_ite (starRingEnd ℂ), map_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
  obtain ⟨r, a, c, b⟩ := p
  obtain ⟨r', a', c', b'⟩ := p'
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases r <;> cases a <;> cases c <;> cases b <;> cases r' <;> cases a' <;> cases c' <;> cases b' <;>
    simp [catState]

lemma g74d_tn0 {ι : Type*} [Fintype ι] [DecidableEq ι] : traceNorm (0 : Matrix ι ι ℂ) = 0 := by
  simp [traceNorm, cfc_zero]

lemma g74d_ach : RedistributionAchievable catState 0 0 := by
  refine ⟨le_refl 0, fun eps heps delta hdelta => ⟨1, fun n _ _ => ⟨g74d_code n, ?_, ?_, ?_⟩⟩⟩
  · unfold TransferCode.redistributionError
    rw [g74d_out, sub_self, g74d_tn0]
    exact heps.le
  · show ((0 : ℕ) : ℝ) ≤ n * (0 + delta)
    push_cast
    positivity
  · show ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) ≤ n * (0 + delta)
    push_cast
    simp only [sub_self, zero_add]
    positivity

theorem solution :
    IsState catState ∧ IsChannel catAlice ∧ IsChannel catBob ∧
    idTensorSuperop (localProduct catAlice catBob) catInput = pureDensity catState ∧
    quantumCost catState = 0 ∧ redistributionEntanglementRate catState = 0 ∧
    RedistributionAchievable catState 0 0 :=
  ⟨g74d_state, g74d_alice_ch, g74d_bob_ch, g74d_oneshot, g74d_costs.1, g74d_costs.2, g74d_ach⟩

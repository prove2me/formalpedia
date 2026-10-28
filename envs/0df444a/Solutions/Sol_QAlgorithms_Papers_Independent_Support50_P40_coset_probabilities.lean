-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P40.coset_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:19:14.438989+00:00
-- url     : https://prove2.me/submissions/794f1297-0bd4-4612-a99c-10b3a1cd5e0c

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Papers.Independent.Support50.P40
open scoped ComplexConjugate Matrix

noncomputable section

def p40tens {n : ℕ} (M : Fin n → Matrix Bool Bool ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => ∏ q, M q (y q) (z q)

lemma p40tens_mul {n : ℕ} (M N : Fin n → Matrix Bool Bool ℂ) :
    p40tens M * p40tens N = p40tens (fun q => M q * N q) := by
  ext y z
  simp only [p40tens, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [Finset.prod_mul_distrib]

lemma p40tens_one {n : ℕ} : p40tens (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  simp only [p40tens, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma p40tens_ct {n : ℕ} (M : Fin n → Matrix Bool Bool ℂ) :
    (p40tens M)ᴴ = p40tens (fun q => (M q)ᴴ) := by
  ext y z
  simp [p40tens, Matrix.conjTranspose_apply]

lemma p40tens_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix Bool Bool ℂ) :
    p40tens (fun q => c q • M q) = (∏ q, c q) • p40tens M := by
  ext y z
  simp [p40tens, Finset.prod_mul_distrib]

lemma p40_pauliOps_eq {n : ℕ} (e : ErrorLabel n) : pauliOps e = p40tens (fun q => (e q).mat) := by
  ext y z
  simp [pauliOps, PauliString.toMatrix, p40tens]

def p40sg (a b : Pauli) : ℂ := if a = .I ∨ b = .I ∨ a = b then 1 else -1

lemma p40_mat_mul (a b : Pauli) :
    a.mat * b.mat = (Complex.I ^ (Pauli.mul a b).1.val) • (Pauli.mul a b).2.mat := by
  have h1 : (1 : ZMod 4).val = 1 := rfl
  have h3 : (3 : ZMod 4).val = 3 := rfl
  cases a <;> cases b <;> ext i j <;> cases i <;> cases j <;>
    simp [Pauli.mat, Pauli.mul, pauliX, pauliY, pauliZ, Matrix.mul_apply, h1, h3, pow_succ]

lemma p40_mat_ct (a : Pauli) : (a.mat)ᴴ = a.mat := by
  cases a <;> ext i j <;> cases i <;> cases j <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

lemma p40_mat_comm (a b : Pauli) : a.mat * b.mat = p40sg a b • (b.mat * a.mat) := by
  cases a <;> cases b <;> ext i j <;> cases i <;> cases j <;>
    simp [p40sg, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply]

lemma p40_mat_sq (a : Pauli) : a.mat * a.mat = 1 := by
  cases a <;> ext i j <;> cases i <;> cases j <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply]

def p40idL (p : ℕ) : ErrorLabel p := fun _ => Pauli.I

lemma p40_lm_comm {p : ℕ} (a b : ErrorLabel p) : labelMul a b = labelMul b a := by
  funext q; simp only [labelMul]; cases a q <;> cases b q <;> rfl

lemma p40_lm_assoc {p : ℕ} (a b c : ErrorLabel p) :
    labelMul (labelMul a b) c = labelMul a (labelMul b c) := by
  funext q; simp only [labelMul]; cases a q <;> cases b q <;> cases c q <;> rfl

lemma p40_lm_self {p : ℕ} (a : ErrorLabel p) : labelMul a a = p40idL p := by
  funext q; simp only [labelMul, p40idL]; cases a q <;> rfl

lemma p40_lm_id {p : ℕ} (a : ErrorLabel p) : labelMul (p40idL p) a = a := by
  funext q; simp only [labelMul, p40idL]; cases a q <;> rfl

lemma p40_lm_cancel {p : ℕ} (a e : ErrorLabel p) : labelMul a (labelMul a e) = e := by
  rw [← p40_lm_assoc, p40_lm_self, p40_lm_id]

lemma p40_mem_coset {p : ℕ} {a e : ErrorLabel p} {A : Finset (ErrorLabel p)} :
    e ∈ labelCoset a A ↔ labelMul a e ∈ A := by
  simp only [labelCoset, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; rwa [p40_lm_cancel]
  · intro h; exact ⟨_, h, p40_lm_cancel a e⟩

def P40Ph (z : ℂ) : Prop := starRingEnd ℂ z * z = 1

lemma p40ph_one : P40Ph 1 := by simp [P40Ph]
lemma p40ph_mul {a b : ℂ} (ha : P40Ph a) (hb : P40Ph b) : P40Ph (a * b) := by
  unfold P40Ph at *; rw [map_mul]
  calc starRingEnd ℂ a * starRingEnd ℂ b * (a * b) = (starRingEnd ℂ a * a) * (starRingEnd ℂ b * b) := by ring
    _ = 1 := by rw [ha, hb, one_mul]
lemma p40ph_conj {a : ℂ} (ha : P40Ph a) : P40Ph (starRingEnd ℂ a) := by
  unfold P40Ph at *; rw [Complex.conj_conj, mul_comm, ha]
lemma p40ph_Ipow (k : ℕ) : P40Ph (Complex.I ^ k) := by
  induction k with
  | zero => simp [P40Ph]
  | succ k ih => rw [pow_succ]; exact p40ph_mul ih (by simp [P40Ph])
lemma p40ph_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i, P40Ph (f i)) :
    P40Ph (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using p40ph_one
  | insert a s ha ih => rw [Finset.prod_insert ha]; exact p40ph_mul (h a) ih

lemma p40_pO_mul {p : ℕ} (a b : ErrorLabel p) : pauliOps a * pauliOps b =
    (∏ q, Complex.I ^ (Pauli.mul (a q) (b q)).1.val) • pauliOps (labelMul a b) := by
  rw [p40_pauliOps_eq, p40_pauliOps_eq, p40_pauliOps_eq, p40tens_mul, ← p40tens_smul]
  congr 1; funext q; exact p40_mat_mul _ _

lemma p40_pO_ct {p : ℕ} (a : ErrorLabel p) : (pauliOps a)ᴴ = pauliOps a := by
  rw [p40_pauliOps_eq, p40tens_ct]; simp [p40_mat_ct]

lemma p40_pO_sq {p : ℕ} (a : ErrorLabel p) : pauliOps a * pauliOps a = 1 := by
  rw [p40_pauliOps_eq, p40tens_mul]; simp [p40_mat_sq, p40tens_one]

lemma p40_pO_id {p : ℕ} : pauliOps (p40idL p) = 1 := by
  rw [p40_pauliOps_eq]; simp [p40idL, Pauli.mat, p40tens_one]

lemma p40_pO_comm {p : ℕ} (a b : ErrorLabel p) : pauliOps a * pauliOps b =
    (∏ q, p40sg (a q) (b q)) • (pauliOps b * pauliOps a) := by
  rw [p40_pauliOps_eq, p40_pauliOps_eq, p40tens_mul, p40tens_mul, ← p40tens_smul]
  congr 1; funext q; exact p40_mat_comm _ _

lemma p40_sg_pm {p : ℕ} (a b : ErrorLabel p) (s : Finset (Fin p)) :
    (∏ q ∈ s, p40sg (a q) (b q)) = 1 ∨ (∏ q ∈ s, p40sg (a q) (b q)) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    rcases ih with h | h <;> rw [h] <;> unfold p40sg <;> split_ifs <;> simp

lemma p40_pO_mul' {p : ℕ} (a b : ErrorLabel p) : ∃ c, P40Ph c ∧
    pauliOps (labelMul a b) = c • (pauliOps a * pauliOps b) := by
  set d := ∏ q, Complex.I ^ (Pauli.mul (a q) (b q)).1.val
  have hd : P40Ph d := p40ph_prod _ _ (fun _ => p40ph_Ipow _)
  refine ⟨starRingEnd ℂ d, p40ph_conj hd, ?_⟩
  rw [p40_pO_mul, smul_smul, hd, one_smul]

lemma p40_mem_pauliGroup {n : ℕ} {U : Matrix.unitaryGroup (Qubits n) ℂ} (h : U ∈ pauliGroup n) :
    ∃ c : ℂ, ∃ e : ErrorLabel n, (U : Matrix (Qubits n) (Qubits n) ℂ) = c • pauliOps e := by
  unfold pauliGroup at h
  induction h using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨P, hP⟩ := hx
    refine ⟨Complex.I ^ P.phase.val, P.ops, ?_⟩
    rw [hP]; ext y z; simp [PauliString.toMatrix, pauliOps]
  | one => exact ⟨1, p40idL n, by simp [p40_pO_id]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, a, ha⟩ := hx
    obtain ⟨d, b, hb⟩ := hy
    refine ⟨c * d * ∏ q, Complex.I ^ (Pauli.mul (a q) (b q)).1.val, labelMul a b, ?_⟩
    rw [Submonoid.coe_mul, ha, hb, smul_mul_smul_comm, p40_pO_mul, smul_smul]
  | inv x _ hx =>
    obtain ⟨c, a, ha⟩ := hx
    refine ⟨starRingEnd ℂ c, a, ?_⟩
    have hx : ((x⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) =
        (x : Matrix (Qubits n) (Qubits n) ℂ)ᴴ := rfl
    rw [hx, ha, Matrix.conjTranspose_smul, p40_pO_ct]; rfl

section codeLemmas
variable {m : ℕ} (C : InnerCode m)

lemma p40_VV : (innerEncoderMatrix C)ᴴ * innerEncoderMatrix C = 1 := by
  have ho := orthonormal_iff_ite.mp C.orthonormal
  ext b b'
  have := ho b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, innerEncoderMatrix, Matrix.one_apply]
  rw [← this]
  simp [PiLp.inner_apply, mul_comm]

lemma p40_VV' (Z : Matrix Bool Bool ℂ) :
    (innerEncoderMatrix C)ᴴ * (innerEncoderMatrix C * Z) = Z := by
  rw [← Matrix.mul_assoc, p40_VV, Matrix.one_mul]

lemma p40_UV (U : Matrix.unitaryGroup (Qubits (m+1)) ℂ) (hU : U ∈ C.stabilizer) :
    (U : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) * innerEncoderMatrix C = innerEncoderMatrix C := by
  ext x b
  have hb : C.basis b ∈ stabilizedSpace C.stabilizer := C.basisSpan ▸ Submodule.subset_span ⟨b, rfl⟩
  simp only [stabilizedSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hb
  have := congrArg (fun w => w x) (hb U hU)
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct] at this
  simp [Matrix.mul_apply, innerEncoderMatrix]
  exact sub_eq_zero.mp this

lemma p40_VU (U : Matrix.unitaryGroup (Qubits (m+1)) ℂ) (hU : U ∈ C.stabilizer) :
    (innerEncoderMatrix C)ᴴ * (U : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) = (innerEncoderMatrix C)ᴴ := by
  have h := p40_UV C U⁻¹ (C.stabilizer.inv_mem hU)
  have hx : ((U⁻¹ : Matrix.unitaryGroup (Qubits (m+1)) ℂ) : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) =
      (U : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ)ᴴ := rfl
  rw [hx] at h
  have := congrArg Matrix.conjTranspose h
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this

lemma p40_anti_zero (X : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ)
    (U : Matrix.unitaryGroup (Qubits (m+1)) ℂ) (hU : U ∈ C.stabilizer)
    (h : X * U = -((U : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) * X)) :
    (innerEncoderMatrix C)ᴴ * X * innerEncoderMatrix C = 0 := by
  have hUV := p40_UV C U hU
  have hVU := p40_VU C U hU
  set V := innerEncoderMatrix C
  have e1 : Vᴴ * X * V = -(Vᴴ * X * V) := by
    calc Vᴴ * X * V = Vᴴ * (X * (U : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ)) * V := by
          simp only [Matrix.mul_assoc, hUV]
      _ = -(Vᴴ * (U : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) * X * V) := by
          rw [h]; simp [Matrix.mul_assoc]
      _ = -(Vᴴ * X * V) := by rw [hVU]
  ext a b
  have := congrFun (congrFun e1 a) b
  simp only [Matrix.neg_apply, Matrix.zero_apply] at this ⊢
  exact self_eq_neg.mp this

lemma p40_memN {g : ErrorLabel (m+1)} :
    g ∈ centralizerLabels C.stabilizer ↔ ∀ U ∈ C.stabilizer,
      pauliOps g * (U : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) = U * pauliOps g := by
  simp [centralizerLabels]

lemma p40_memSl {s : ErrorLabel (m+1)} :
    s ∈ stabilizerLabels C.stabilizer ↔ ∃ U ∈ C.stabilizer, ∃ c : ZMod 4,
      pauliOps s = Complex.I ^ c.val • (U : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) := by
  simp [stabilizerLabels]

lemma p40_notN {g : ErrorLabel (m+1)} (hg : g ∉ centralizerLabels C.stabilizer) :
    (innerEncoderMatrix C)ᴴ * pauliOps g * innerEncoderMatrix C = 0 := by
  rw [p40_memN] at hg
  push_neg at hg
  obtain ⟨U, hU, hne⟩ := hg
  obtain ⟨c, a, ha⟩ := p40_mem_pauliGroup (C.valid.1 hU)
  apply p40_anti_zero C _ U hU
  rw [ha] at hne ⊢
  rw [Matrix.mul_smul, Matrix.smul_mul, p40_pO_comm g a] at hne ⊢
  rcases p40_sg_pm g a Finset.univ with h | h
  · rw [h, one_smul] at hne; exact absurd rfl hne
  · rw [h]; simp

lemma p40_SlN {s : ErrorLabel (m+1)} (hs : s ∈ stabilizerLabels C.stabilizer) :
    s ∈ centralizerLabels C.stabilizer := by
  rw [p40_memSl] at hs
  obtain ⟨U, hU, c, hc⟩ := hs
  rw [p40_memN]
  intro U' hU'
  have hcomm := congrArg (fun W : Matrix.unitaryGroup (Qubits (m+1)) ℂ =>
    (W : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ)) (C.valid.2.1 U hU U' hU')
  simp only [Submonoid.coe_mul] at hcomm
  rw [hc, Matrix.smul_mul, Matrix.mul_smul, hcomm]

lemma p40_mulN {a b : ErrorLabel (m+1)} (ha : a ∈ centralizerLabels C.stabilizer)
    (hb : b ∈ centralizerLabels C.stabilizer) : labelMul a b ∈ centralizerLabels C.stabilizer := by
  rw [p40_memN] at *
  intro U hU
  obtain ⟨c, _, hc⟩ := p40_pO_mul' a b
  rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hb U hU, ← Matrix.mul_assoc, ha U hU,
    Matrix.mul_assoc]

lemma p40_SlV {s : ErrorLabel (m+1)} (hs : s ∈ stabilizerLabels C.stabilizer) :
    ∃ c, P40Ph c ∧ pauliOps s * innerEncoderMatrix C = c • innerEncoderMatrix C := by
  rw [p40_memSl] at hs
  obtain ⟨U, hU, c, hc⟩ := hs
  exact ⟨_, p40ph_Ipow c.val, by rw [hc, Matrix.smul_mul, p40_UV C U hU]⟩

lemma p40_scal (B : Matrix Bool Bool ℂ) (h : ∀ ρ, B * ρ * Bᴴ = ρ) : ∃ c, P40Ph c ∧ B = c • 1 := by
  have key : ∀ a b x y, B x a * starRingEnd ℂ (B y b) = if x = a ∧ y = b then 1 else 0 := by
    intro a b x y
    have := congrFun (congrFun (h (Matrix.single a b 1)) x) y
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply] at this
    cases a <;> cases b <;> cases x <;> cases y <;> simpa using this
  have off : ∀ x a, x ≠ a → B x a = 0 := by
    intro x a hxa
    have := key a a x x
    rw [if_neg (by tauto)] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · simpa using h1
  have d1 := key false false false false
  have d2 := key true false true false
  simp at d1 d2
  refine ⟨B false false, by unfold P40Ph; rw [mul_comm]; exact d1, ?_⟩
  have htt : B true true = B false false := by
    have hne : starRingEnd ℂ (B false false) ≠ 0 := by
      intro h0; rw [h0] at d1; simp at d1
    exact mul_right_cancel₀ hne (d2.trans d1.symm)
  ext x y
  cases x <;> cases y <;> simp [htt, off]

end codeLemmas

lemma p40_smconj {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ℂ} (hc : P40Ph c) (A : Matrix κ ι ℂ)
    (ρ : Matrix ι ι ℂ) : (c • A) * ρ * (c • A)ᴴ = A * ρ * Aᴴ := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  unfold P40Ph at hc
  have : star c * c = 1 := hc
  rw [mul_comm, this, one_smul]

lemma p40_dist {j k : Pauli}
    (h : j.mat * Matrix.single false true 1 * (j.mat)ᴴ = k.mat * Matrix.single false true 1 * (k.mat)ᴴ) :
    j = k := by
  have h1 := congrFun (congrFun h false) true
  have h2 := congrFun (congrFun h true) false
  cases j <;> cases k <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.single_apply,
      Matrix.conjTranspose_apply] at h1 h2 ⊢
  all_goals (revert h1 h2; norm_num)

section logicLemmas
variable {m : ℕ} {C : InnerCode m} (T : CosetChoices C)

lemma p40_sand (A : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) (ρ X : Matrix Bool Bool ℂ)
    (h : A * (innerEncoderMatrix C * ρ * (innerEncoderMatrix C)ᴴ) * Aᴴ =
      innerEncoderMatrix C * X * (innerEncoderMatrix C)ᴴ) :
    ((innerEncoderMatrix C)ᴴ * A * innerEncoderMatrix C) * ρ *
      ((innerEncoderMatrix C)ᴴ * A * innerEncoderMatrix C)ᴴ = X := by
  have h2 := congrArg (fun Z => (innerEncoderMatrix C)ᴴ * Z * innerEncoderMatrix C) h
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] at h2 ⊢
  rw [p40_VV' C, p40_VV C, Matrix.mul_one] at h2
  exact h2

lemma p40_logic (k : Pauli) : ∃ c, P40Ph c ∧
    (innerEncoderMatrix C)ᴴ * pauliOps (T.logicalRep k) * innerEncoderMatrix C = c • k.mat := by
  set A := (innerEncoderMatrix C)ᴴ * pauliOps (T.logicalRep k) * innerEncoderMatrix C with hAdef
  have hA : ∀ ρ, A * ρ * Aᴴ = k.mat * ρ * (k.mat)ᴴ := fun ρ => p40_sand _ _ _ (T.logicalAction k ρ)
  obtain ⟨c, hc, hB⟩ := p40_scal (k.mat * A) (by
    intro ρ
    rw [Matrix.conjTranspose_mul, p40_mat_ct]
    calc k.mat * A * ρ * (Aᴴ * k.mat) = k.mat * (A * ρ * Aᴴ) * k.mat := by simp [Matrix.mul_assoc]
      _ = ρ := by rw [hA, p40_mat_ct]; simp only [← Matrix.mul_assoc, p40_mat_sq, Matrix.one_mul]
                  rw [Matrix.mul_assoc, p40_mat_sq, Matrix.mul_one])
  refine ⟨c, hc, ?_⟩
  calc A = k.mat * (k.mat * A) := by rw [← Matrix.mul_assoc, p40_mat_sq, Matrix.one_mul]
    _ = c • k.mat := by rw [hB, Matrix.mul_smul, Matrix.mul_one]

lemma p40_cosetV {k : Pauli} {e : ErrorLabel (m+1)}
    (he : e ∈ labelCoset (T.logicalRep k) (stabilizerLabels C.stabilizer)) :
    ∃ c, P40Ph c ∧ pauliOps e * innerEncoderMatrix C =
      c • (pauliOps (T.logicalRep k) * innerEncoderMatrix C) := by
  rw [p40_mem_coset] at he
  obtain ⟨c2, hc2, h2⟩ := p40_SlV C he
  obtain ⟨c1, hc1, h1⟩ := p40_pO_mul' (T.logicalRep k) (labelMul (T.logicalRep k) e)
  rw [p40_lm_cancel] at h1
  refine ⟨c1 * c2, p40ph_mul hc1 hc2, ?_⟩
  rw [h1, Matrix.smul_mul, Matrix.mul_assoc, h2, Matrix.mul_smul, smul_smul]

lemma p40_key {k : Pauli} {g : ErrorLabel (m+1)}
    (hg : g ∈ labelCoset (T.logicalRep k) (stabilizerLabels C.stabilizer)) :
    ∃ c, P40Ph c ∧ (innerEncoderMatrix C)ᴴ * pauliOps g * innerEncoderMatrix C = c • k.mat := by
  obtain ⟨c1, hc1, h1⟩ := p40_cosetV T hg
  obtain ⟨c2, hc2, h2⟩ := p40_logic T k
  refine ⟨c1 * c2, p40ph_mul hc1 hc2, ?_⟩
  rw [Matrix.mul_assoc, h1, Matrix.mul_smul, ← Matrix.mul_assoc, h2, smul_smul]

lemma p40_cosetN {k : Pauli} {g : ErrorLabel (m+1)}
    (hg : g ∈ labelCoset (T.logicalRep k) (stabilizerLabels C.stabilizer)) :
    g ∈ centralizerLabels C.stabilizer := by
  rw [p40_mem_coset] at hg
  have := p40_mulN C (T.logicalCentralizes k) (p40_SlN C hg)
  rwa [p40_lm_cancel] at this

lemma p40_LI : T.logicalRep .I = p40idL (m+1) := T.logicalIdentity

lemma p40_cosetI {g : ErrorLabel (m+1)} :
    g ∈ labelCoset (T.logicalRep .I) (stabilizerLabels C.stabilizer) ↔
      g ∈ stabilizerLabels C.stabilizer := by
  rw [p40_mem_coset, p40_LI, p40_lm_id]

end logicLemmas

lemma p40_conj_vmv {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Matrix κ ι ℂ) (a b : ι → ℂ) (x x' : κ) :
    (P * Matrix.vecMulVec a (star b) * Pᴴ) x x' = (P *ᵥ a) x * star ((P *ᵥ b) x') := by
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Pi.star_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring

def p40w (p : ℕ) (f : ℝ) (e : ErrorLabel p) : ℝ := f ^ (p - opsWeight e) * noiseG f ^ opsWeight e

lemma p40_wp_eq {p : ℕ} (f : ℝ) (A : Finset (ErrorLabel p)) :
    weightPolynomial f A = ∑ e, if e ∈ A then p40w p f e else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]; rfl

section outputs
variable {m : ℕ} (C : InnerCode m)

def p40u (e : ErrorLabel (m+1)) : Bool × Qubits (m+1) → ℂ :=
  fun rx => (pauliOps e * innerEncoderMatrix C) rx.2 rx.1

lemma p40_bell_entry (rx : Bool × Qubits (m+1)) :
    codeBellInput C rx = ((Real.sqrt 2)⁻¹ : ℂ) * innerEncoderMatrix C rx.2 rx.1 := by
  obtain ⟨r, x⟩ := rx
  cases r <;> simp [codeBellInput, tensorVec, ket, innerEncoderMatrix]

lemma p40_outputRQ (f : ℝ) : outputRQ C f =
    ∑ e, ((p40w (m+1) f e / 2 : ℝ) : ℂ) • Matrix.vecMulVec (p40u C e) (star (p40u C e)) := by
  ext ⟨r, x⟩ ⟨r', x'⟩
  simp only [outputRQ, idTensorSuperop, independentPauliChannel, conjSuperop, Matrix.of_apply,
    Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hB : (Matrix.of fun i i' => pureDensity (codeBellInput C) (r, i) (r', i')) =
      ((1 / 2 : ℝ) : ℂ) • Matrix.vecMulVec (fun i => innerEncoderMatrix C i r)
        (star fun i => innerEncoderMatrix C i r') := by
    ext i i'
    simp only [pureDensity, Matrix.of_apply, p40_bell_entry, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, map_mul]
    have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * starRingEnd ℂ ((Real.sqrt 2)⁻¹ : ℂ) = ((1/2 : ℝ) : ℂ) := by
      rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      push_cast; ring
    rw [← h2]; simp only [RCLike.star_def]; ring
  rw [hB, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, p40_conj_vmv]
  simp only [p40u, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, p40w, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one]
  ring

lemma p40_outputQ (f : ℝ) : outputQ C f =
    ∑ e, ((p40w (m+1) f e / 2 : ℝ) : ℂ) •
      ((pauliOps e * innerEncoderMatrix C) * (pauliOps e * innerEncoderMatrix C)ᴴ) := by
  rw [outputQ, p40_outputRQ]
  ext x x'
  simp only [traceLeft, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1

end outputs

lemma p40_eff_sum {ι E : Type*} [Fintype ι] [Fintype E] (M : Matrix ι ι ℂ) (r : E → ℝ)
    (X : E → Matrix ι ι ℂ) :
    effectProb M (∑ e, ((r e : ℝ) : ℂ) • X e) = ∑ e, r e * effectProb M (X e) := by
  simp [effectProb, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]

lemma p40_eff_pure {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) (u : ι → ℂ) :
    effectProb (pureDensity ψ) (Matrix.vecMulVec u (star u)) =
      Complex.normSq (∑ a, starRingEnd ℂ (ψ a) * u a) := by
  have : (pureDensity ψ * Matrix.vecMulVec u (star u)).trace =
      starRingEnd ℂ (∑ a, starRingEnd ℂ (ψ a) * u a) * (∑ a, starRingEnd ℂ (ψ a) * u a) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [RCLike.star_def]; ring
  rw [effectProb, this, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

section final
variable {m : ℕ} {C : InnerCode m} (T : CosetChoices C)

lemma p40_reassoc (A : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ) (ρ : Matrix Bool Bool ℂ) :
    A * (innerEncoderMatrix C * ρ * (innerEncoderMatrix C)ᴴ) * Aᴴ =
      (A * innerEncoderMatrix C) * ρ * (A * innerEncoderMatrix C)ᴴ := by
  rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

lemma p40_Ae_zero (a e : ErrorLabel (m+1)) (h : labelMul a e ∉ centralizerLabels C.stabilizer) :
    (innerEncoderMatrix C)ᴴ * (pauliOps a * pauliOps e) * innerEncoderMatrix C = 0 := by
  rw [p40_pO_mul, Matrix.mul_smul, Matrix.smul_mul, p40_notN C h, smul_zero]

lemma p40_Ae_log (a e : ErrorLabel (m+1)) (k : Pauli)
    (h : labelMul a e ∈ labelCoset (T.logicalRep k) (stabilizerLabels C.stabilizer)) :
    ∃ c, P40Ph c ∧ (innerEncoderMatrix C)ᴴ * (pauliOps a * pauliOps e) * innerEncoderMatrix C =
      c • k.mat := by
  obtain ⟨c, hc, hk⟩ := p40_key T h
  refine ⟨(∏ q, Complex.I ^ (Pauli.mul (a q) (e q)).1.val) * c,
    p40ph_mul (p40ph_prod _ _ (fun _ => p40ph_Ipow _)) hc, ?_⟩
  rw [p40_pO_mul, Matrix.mul_smul, Matrix.smul_mul, hk, smul_smul]

lemma p40_coset_shift {p : ℕ} (a b e : ErrorLabel p) (A : Finset (ErrorLabel p)) :
    e ∈ labelCoset (labelMul a b) A ↔ labelMul a e ∈ labelCoset b A := by
  rw [p40_mem_coset, p40_mem_coset, p40_lm_comm a b, p40_lm_assoc]

lemma p40_coset_id {p : ℕ} (A : Finset (ErrorLabel p)) : labelCoset (p40idL p) A = A := by
  ext e; rw [p40_mem_coset, p40_lm_id]

include T in
lemma p40_R1 (e : ErrorLabel (m+1)) : e ∈ stabilizerLabels C.stabilizer ↔
    ∀ ρ : Matrix Bool Bool ℂ, conjSuperop (pauliOps e) (conjSuperop (innerEncoderMatrix C) ρ) =
      conjSuperop (innerEncoderMatrix C) ρ := by
  constructor
  · intro hs ρ
    obtain ⟨c, hc, h⟩ := p40_SlV C hs
    show pauliOps e * (innerEncoderMatrix C * ρ * (innerEncoderMatrix C)ᴴ) * (pauliOps e)ᴴ =
      innerEncoderMatrix C * ρ * (innerEncoderMatrix C)ᴴ
    rw [p40_reassoc, h, p40_smconj hc]
  · intro h
    by_cases hN : e ∈ centralizerLabels C.stabilizer
    · obtain ⟨k, hk, -⟩ := T.logicalTransversal e hN
      obtain ⟨c, hc, hkey⟩ := p40_key T hk
      have h1 := p40_sand (pauliOps e) (Matrix.single false true 1) _ (h (Matrix.single false true 1))
      rw [hkey, p40_smconj hc] at h1
      have hkI : k = .I := p40_dist (by rw [h1]; simp [Pauli.mat])
      subst hkI
      exact (p40_cosetI T).mp hk
    · exfalso
      have h1 := p40_sand (pauliOps e) 1 _ (h 1)
      rw [p40_notN C hN] at h1
      have := congrFun (congrFun h1 false) false
      simp at this

lemma p40_R2 (j : Pauli) (e : ErrorLabel (m+1)) :
    e ∈ labelCoset (T.logicalRep j) (stabilizerLabels C.stabilizer) ↔
      (e ∈ centralizerLabels C.stabilizer ∧ ∀ ρ : Matrix Bool Bool ℂ,
        conjSuperop (pauliOps e) (conjSuperop (innerEncoderMatrix C) ρ) =
          conjSuperop (innerEncoderMatrix C) (conjSuperop j.mat ρ)) := by
  constructor
  · intro he
    refine ⟨p40_cosetN T he, fun ρ => ?_⟩
    obtain ⟨c, hc, h⟩ := p40_cosetV T he
    show pauliOps e * (innerEncoderMatrix C * ρ * (innerEncoderMatrix C)ᴴ) * (pauliOps e)ᴴ =
      innerEncoderMatrix C * (j.mat * ρ * (j.mat)ᴴ) * (innerEncoderMatrix C)ᴴ
    rw [p40_reassoc, h, p40_smconj hc, ← p40_reassoc]
    exact T.logicalAction j ρ
  · rintro ⟨hN, h⟩
    obtain ⟨k, hk, -⟩ := T.logicalTransversal e hN
    obtain ⟨c, hc, hkey⟩ := p40_key T hk
    have h1 := p40_sand (pauliOps e) (Matrix.single false true 1) _ (h (Matrix.single false true 1))
    rw [hkey, p40_smconj hc] at h1
    rwa [← p40_dist h1]

lemma p40_tr_k (k : Pauli) : (k.mat).trace = if k = .I then 2 else 0 := by
  cases k <;> simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.trace, Fintype.sum_bool] <;> norm_num

lemma p40_trace4 {ι κ : Type*} [Fintype ι] [Fintype κ] (W Y : Matrix ι κ ℂ) :
    (W * Wᴴ * (Y * Yᴴ)).trace = ((Wᴴ * Y) * (Wᴴ * Y)ᴴ).trace := by
  calc (W * Wᴴ * (Y * Yᴴ)).trace = (W * (Wᴴ * Y * Yᴴ)).trace := by simp only [Matrix.mul_assoc]
    _ = ((Wᴴ * Y * Yᴴ) * W).trace := Matrix.trace_mul_comm _ _
    _ = ((Wᴴ * Y) * (Wᴴ * Y)ᴴ).trace := by
        rw [Matrix.conjTranspose_mul (Wᴴ) Y, Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]

include T in
lemma p40_R4 (a e : ErrorLabel (m+1)) :
    effectProb ((pauliOps a * innerEncoderMatrix C) * (pauliOps a * innerEncoderMatrix C)ᴴ)
      ((pauliOps e * innerEncoderMatrix C) * (pauliOps e * innerEncoderMatrix C)ᴴ) =
      if e ∈ labelCoset a (centralizerLabels C.stabilizer) then 2 else 0 := by
  set A := (innerEncoderMatrix C)ᴴ * (pauliOps a * pauliOps e) * innerEncoderMatrix C with hAdef
  have hA : (pauliOps a * innerEncoderMatrix C)ᴴ * (pauliOps e * innerEncoderMatrix C) = A := by
    rw [hAdef, Matrix.conjTranspose_mul, p40_pO_ct]; simp only [Matrix.mul_assoc]
  have htr : ((pauliOps a * innerEncoderMatrix C) * (pauliOps a * innerEncoderMatrix C)ᴴ *
      ((pauliOps e * innerEncoderMatrix C) * (pauliOps e * innerEncoderMatrix C)ᴴ)).trace =
      (A * Aᴴ).trace := by
    rw [p40_trace4, hA]
  rw [effectProb, htr]
  by_cases hN : labelMul a e ∈ centralizerLabels C.stabilizer
  · obtain ⟨k, hk, -⟩ := T.logicalTransversal _ hN
    obtain ⟨c, hc, hAk⟩ := p40_Ae_log T a e k hk
    rw [if_pos (p40_mem_coset.mpr hN), hAdef, hAk]
    have := p40_smconj hc k.mat 1
    rw [Matrix.mul_one, Matrix.mul_one] at this
    rw [this, p40_mat_ct, p40_mat_sq]
    simp
  · rw [if_neg (fun h => hN (p40_mem_coset.mp h)), hAdef, p40_Ae_zero a e hN]
    simp

include T in
lemma p40_R5 (q e : ErrorLabel (m+1)) :
    Complex.normSq ((innerEncoderMatrix C)ᴴ * (pauliOps q * pauliOps e) * innerEncoderMatrix C).trace =
      if e ∈ labelCoset q (stabilizerLabels C.stabilizer) then 4 else 0 := by
  simp only [p40_mem_coset]
  by_cases hN : labelMul q e ∈ centralizerLabels C.stabilizer
  · obtain ⟨k, hk, huniq⟩ := T.logicalTransversal _ hN
    obtain ⟨c, hc, hAk⟩ := p40_Ae_log T q e k hk
    have hc1 : Complex.normSq c = 1 := by
      have : ((Complex.normSq c : ℝ) : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact hc
      exact_mod_cast this
    rw [hAk, Matrix.trace_smul, smul_eq_mul, Complex.normSq_mul, hc1, one_mul, p40_tr_k]
    by_cases hkI : k = .I
    · subst hkI
      rw [if_pos rfl, if_pos ((p40_cosetI T).mp hk)]
      norm_num [Complex.normSq]
    · rw [if_neg hkI, if_neg]
      · simp
      · intro hS
        exact hkI (huniq _ ((p40_cosetI T).mpr hS)).symm
  · rw [p40_Ae_zero q e hN, if_neg (fun hS => hN (p40_SlN C hS))]
    simp

lemma p40_R6 (i : Qubits m) (e : ErrorLabel (m+1)) (ρ : Matrix Bool Bool ℂ) :
    ((innerEncoderMatrix C)ᴴ * (pauliOps (T.syndromeRep i) * pauliOps e) * innerEncoderMatrix C) * ρ *
      ((innerEncoderMatrix C)ᴴ * (pauliOps (T.syndromeRep i) * pauliOps e) * innerEncoderMatrix C)ᴴ =
      ∑ j : Pauli, (if e ∈ labelCoset (labelMul (T.syndromeRep i) (T.logicalRep j))
        (stabilizerLabels C.stabilizer) then (1 : ℂ) else 0) • (j.mat * ρ * (j.mat)ᴴ) := by
  simp_rw [p40_coset_shift]
  by_cases hN : labelMul (T.syndromeRep i) e ∈ centralizerLabels C.stabilizer
  · obtain ⟨k, hk, huniq⟩ := T.logicalTransversal _ hN
    obtain ⟨c, hc, hAk⟩ := p40_Ae_log T _ e k hk
    rw [hAk, p40_smconj hc, Finset.sum_eq_single k]
    · rw [if_pos hk, one_smul]
    · intro j _ hjk
      rw [if_neg (fun hj => hjk (huniq j hj)), zero_smul]
    · intro h; exact absurd (Finset.mem_univ k) h
  · rw [p40_Ae_zero _ e hN]
    simp only [Matrix.zero_mul, Matrix.conjTranspose_zero, Matrix.mul_zero]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun hj => hN (p40_cosetN T hj)), zero_smul]

end final

section assembly
variable {m : ℕ} {C : InnerCode m} (T : CosetChoices C)

lemma p40_synProj (i : Qubits m) : syndromeProjector C T i =
    (pauliOps (T.syndromeRep i) * innerEncoderMatrix C) *
      (pauliOps (T.syndromeRep i) * innerEncoderMatrix C)ᴴ := by
  ext x x'
  simp [syndromeProjector, pureDensity, errorBasis, act, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    innerEncoderMatrix, Matrix.conjTranspose_apply, Matrix.sum_apply, mul_comm]

lemma p40_bellB_entry (i : Qubits m) (j : Pauli) (rx : Bool × Qubits (m+1)) :
    bellBasis C T i j rx = ((Real.sqrt 2)⁻¹ : ℂ) *
      (pauliOps (labelMul (T.syndromeRep i) (T.logicalRep j)) * innerEncoderMatrix C) rx.2 rx.1 := by
  obtain ⟨r, x⟩ := rx
  simp only [bellBasis, act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.kronecker, Matrix.one_apply, p40_bell_entry, Matrix.mul_apply]
  simp [Finset.mul_sum, mul_comm]
  refine Finset.sum_congr rfl fun _ _ => by ring

lemma p40_rec_expand (f : ℝ) (i : Qubits m) (ρ : Matrix Bool Bool ℂ) :
    recoveredBranch C T f i ρ = ∑ e, ((p40w (m+1) f e : ℝ) : ℂ) •
      (((innerEncoderMatrix C)ᴴ * (pauliOps (T.syndromeRep i) * pauliOps e) * innerEncoderMatrix C) * ρ *
      ((innerEncoderMatrix C)ᴴ * (pauliOps (T.syndromeRep i) * pauliOps e) * innerEncoderMatrix C)ᴴ) := by
  simp only [recoveredBranch, Function.comp, conjSuperop, independentPauliChannel, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [p40w]; congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, p40_pO_ct, Matrix.mul_assoc]

end assembly

theorem solution {m : ℕ} (C : InnerCode m) (T : CosetChoices C)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    weightPolynomial f (stabilizerLabels C.stabilizer) =
      errorEventMass f (fun e : ErrorLabel (m + 1) =>
        ∀ rho : Matrix Bool Bool ℂ,
          conjSuperop (pauliOps e) (conjSuperop (innerEncoderMatrix C) rho) =
            conjSuperop (innerEncoderMatrix C) rho) ∧
    (∀ j : Pauli, j ≠ .I →
      weightPolynomial f (labelCoset (T.logicalRep j) (stabilizerLabels C.stabilizer)) =
        errorEventMass f (fun e : ErrorLabel (m + 1) =>
          e ∈ centralizerLabels C.stabilizer ∧ ∀ rho : Matrix Bool Bool ℂ,
            conjSuperop (pauliOps e) (conjSuperop (innerEncoderMatrix C) rho) =
              conjSuperop (innerEncoderMatrix C) (conjSuperop j.mat rho))) ∧
    weightPolynomial f (centralizerLabels C.stabilizer) =
      effectProb (syndromeProjector C T (fun _ => false)) (outputQ C f) ∧
    (∀ i, syndromeMass C T f i =
      effectProb (syndromeProjector C T i) (outputQ C f)) ∧
    (∀ i j, jointMass C T f i j =
      effectProb (pureDensity (bellBasis C T i j)) (outputRQ C f)) ∧
    (∀ i (rho : Matrix Bool Bool ℂ), recoveredBranch C T f i rho =
      ∑ j : Pauli, (jointMass C T f i j : ℂ) • conjSuperop j.mat rho) := by
  have h4 : ∀ i, syndromeMass C T f i = effectProb (syndromeProjector C T i) (outputQ C f) := by
    intro i
    rw [p40_synProj, p40_outputQ, p40_eff_sum, syndromeMass, p40_wp_eq]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [p40_R4 T]
    split_ifs <;> ring
  refine ⟨?_, ?_, ?_, h4, ?_, ?_⟩
  · unfold errorEventMass
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact p40_R1 T e
  · intro j _
    unfold errorEventMass
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact p40_R2 T j e
  · rw [← h4, syndromeMass, T.syndromeZero]
    exact congrArg _ (p40_coset_id _).symm
  · intro i j
    rw [p40_outputRQ, p40_eff_sum, jointMass, p40_wp_eq]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [p40_eff_pure]
    have hsum : (∑ a, starRingEnd ℂ (bellBasis C T i j a) * p40u C e a) =
        ((Real.sqrt 2)⁻¹ : ℂ) * ((innerEncoderMatrix C)ᴴ *
          (pauliOps (labelMul (T.syndromeRep i) (T.logicalRep j)) * pauliOps e) *
            innerEncoderMatrix C).trace := by
      have hA : (pauliOps (labelMul (T.syndromeRep i) (T.logicalRep j)) * innerEncoderMatrix C)ᴴ *
          (pauliOps e * innerEncoderMatrix C) = (innerEncoderMatrix C)ᴴ *
          (pauliOps (labelMul (T.syndromeRep i) (T.logicalRep j)) * pauliOps e) * innerEncoderMatrix C := by
        rw [Matrix.conjTranspose_mul, p40_pO_ct]; simp only [Matrix.mul_assoc]
      rw [← hA, Fintype.sum_prod_type]
      simp only [p40_bellB_entry, p40u, map_mul, map_inv₀, Complex.conj_ofReal]
      rw [Matrix.trace, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def]; ring
    rw [hsum, Complex.normSq_mul, p40_R5 T]
    have h2 : Complex.normSq ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
      rw [← Complex.ofReal_inv, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
      norm_num
    rw [h2]
    split_ifs <;> ring
  · intro i ρ
    rw [p40_rec_expand]
    simp_rw [p40_R6 T, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul, jointMass, p40_wp_eq]
    simp only [conjSuperop]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp

end

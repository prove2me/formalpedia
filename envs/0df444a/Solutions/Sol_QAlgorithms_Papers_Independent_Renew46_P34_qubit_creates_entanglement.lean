-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P34.qubit_creates_entanglement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:14:27.7362+00:00
-- url     : https://prove2.me/submissions/5d6862fe-28a6-4ca0-bbaa-ffcbb243c0da

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34
noncomputable section
open scoped Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P34

instance g64g_uq : Unique (Qubits 0) := Pi.uniqueOfIsEmpty _

instance g64g_uq2 : Unique ((Qubits 0 × Qubits 0) × (Unit × Qubits 0)) := Unique.mk' _

def g64g_c : ℂ := ((Real.sqrt ((2 : ℝ) ^ 1))⁻¹ : ℂ)

def g64g_bit (b : Qubits 1) : Fin 2 := if b 0 then 1 else 0

def g64g_encK : Fin 1 → Matrix (Unit × (Fin 2 × (Qubits 1 × Qubits 0))) ((Qubits 0 × Qubits 0) × (Unit × Qubits 0)) ℂ :=
  fun _ o _ => if o.2.1 = g64g_bit o.2.2.1 then g64g_c else 0

def g64g_aliceK : Fin 1 → Matrix (Qubits 1) (Unit × Fin 2) ℂ :=
  fun _ b i => if i.2 = g64g_bit b then 1 else 0

def g64g_bobK : Fin 1 → Matrix (Qubits 0 × (Qubits 0 × Qubits 1)) (Unit × (Unit × (Qubits 0 × (Qubits 1 × Qubits 0)))) ℂ :=
  fun _ o i => if o.2.2 = i.2.2.2.1 then 1 else 0

lemma g64g_c_sq : g64g_c * g64g_c = 1 / 2 := by
  unfold g64g_c
  rw [← mul_inv]
  norm_cast
  rw [Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma g64g_bit_bij : Function.Bijective g64g_bit := by
  constructor
  · intro a b h
    funext i
    fin_cases i
    unfold g64g_bit at h
    cases ha : a 0 <;> cases hb : b 0 <;> simp_all
  · intro m
    fin_cases m
    · exact ⟨fun _ => false, by simp [g64g_bit]⟩
    · exact ⟨fun _ => true, by simp [g64g_bit]⟩

lemma g64g_sum_q1 (f : Qubits 1 → ℂ) : ∑ b, f b = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.ofBijective _ g64g_bit_bij).symm.sum_comp, Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> apply (Equiv.ofBijective _ g64g_bit_bij).injective <;>
    simp [g64g_bit]

lemma g64g_k1 {ι κ : Type} [Fintype ι] (E : Fin 1 → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) (i j : κ) :
    krausApply E ρ i j = ∑ a, ∑ b, E 0 i a * ρ a b * conj (E 0 j b) := by
  simp [krausApply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma g64g_c_eq : g64g_c = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  simp [g64g_c]

lemma g64g_bit_inj (a b : Qubits 1) : g64g_bit a = g64g_bit b ↔ a = b :=
  g64g_bit_bij.1.eq_iff

def g64g_psi (o : Unit × (Fin 2 × (Qubits 1 × Qubits 0))) : ℂ :=
  if o.2.1 = g64g_bit o.2.2.1 then g64g_c else 0

def g64g_enc : Superop ((Qubits 0 × Qubits 0) × (Unit × Qubits 0)) (Unit × (Fin 2 × (Qubits 1 × Qubits 0))) :=
  fun ρ => Matrix.of fun o o' => ρ default default * g64g_psi o * conj (g64g_psi o')

def g64g_ali : Superop (Unit × Fin 2) (Qubits 1) :=
  fun ρ => Matrix.of fun b b' => ρ ((), g64g_bit b) ((), g64g_bit b')

def g64g_bob : Superop (Unit × (Unit × (Qubits 0 × (Qubits 1 × Qubits 0)))) (Qubits 0 × (Qubits 0 × Qubits 1)) :=
  fun ρ => Matrix.of fun o o' => ρ ((), ((), (default, (o.2.2, default)))) ((), ((), (default, (o'.2.2, default))))

lemma g64g_perm {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] (f : κ → ι)
    (hf : Function.Bijective f) :
    IsKrausFamily (fun _ : Fin 1 => (Matrix.of fun o i => if i = f o then (1 : ℂ) else 0)) ∧
    ∀ ρ, krausApply (fun _ : Fin 1 => (Matrix.of fun o i => if i = f o then (1 : ℂ) else 0)) ρ =
      Matrix.of fun o o' => ρ (f o) (f o') := by
  constructor
  · unfold IsKrausFamily
    ext a a'
    simp only [Fin.sum_univ_one, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [hf.sum_comp (fun x => star (if a = x then (1 : ℂ) else 0) * (if a' = x then 1 else 0))]
    simp [Matrix.one_apply]
  · intro ρ
    ext o o'
    rw [g64g_k1]
    simp [Matrix.of_apply]

lemma g64g_prep {ι κ : Type} [Fintype ι] [Fintype κ] [Unique ι] [DecidableEq ι] (ψ : κ → ℂ)
    (hψ : ∑ o, star (ψ o) * ψ o = 1) :
    IsKrausFamily (fun _ : Fin 1 => (Matrix.of fun o (_ : ι) => ψ o)) ∧
    ∀ ρ, krausApply (fun _ : Fin 1 => (Matrix.of fun o (_ : ι) => ψ o)) ρ =
      Matrix.of fun o o' => ρ default default * ψ o * conj (ψ o') := by
  constructor
  · unfold IsKrausFamily
    ext a a'
    simp only [Fin.sum_univ_one, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hψ]
    rw [Subsingleton.elim a a']; simp
  · intro ρ
    ext o o'
    rw [g64g_k1]
    simp only [Matrix.of_apply, Fintype.sum_unique]
    ring

lemma g64g_psi_norm : ∑ o, star (g64g_psi o) * g64g_psi o = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_two, g64g_sum_q1]
  simp [g64g_psi, g64g_bit, g64g_c_eq]
  have : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [this]; norm_num

lemma g64g_ali_bij : Function.Bijective (fun b : Qubits 1 => ((), g64g_bit b)) := by
  constructor
  · intro a b h
    exact g64g_bit_bij.1 (congrArg Prod.snd h)
  · intro x
    obtain ⟨b, hb⟩ := g64g_bit_bij.2 x.2
    exact ⟨b, Prod.ext rfl hb⟩

lemma g64g_bob_bij : Function.Bijective (fun o : Qubits 0 × (Qubits 0 × Qubits 1) =>
      ((), ((), ((default : Qubits 0), (o.2.2, (default : Qubits 0)))))) := by
  constructor
  · intro a b h
    have h3 : a.2.2 = b.2.2 := congrArg (fun x => x.2.2.2.1) h
    exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) h3)
  · intro x
    refine ⟨(default, (default, x.2.2.2.1)), ?_⟩
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Prod.ext rfl (Subsingleton.elim _ _))))

def g64g_P : OneWayCode Unit Unit Unit Unit Unit (TaskInput 0 0) (Qubits 1) (TaskBob 0 0 1) where
  e := 0
  q := 1
  c := 0
  memory := 2
  memoryPositive := by norm_num
  encoder := g64g_enc
  aliceDecoder := g64g_ali
  bobDecoder := g64g_bob
  encoderChannel := ⟨1, _, by convert (g64g_prep (ι := (Qubits 0 × Qubits 0) × (Unit × Qubits 0)) g64g_psi g64g_psi_norm).1,
    fun ρ => ((g64g_prep (ι := (Qubits 0 × Qubits 0) × (Unit × Qubits 0)) g64g_psi g64g_psi_norm).2 ρ).symm⟩
  aliceChannel := ⟨1, _, by convert (g64g_perm (fun b : Qubits 1 => ((), g64g_bit b)) g64g_ali_bij).1,
    fun ρ => ((g64g_perm (fun b : Qubits 1 => ((), g64g_bit b)) g64g_ali_bij).2 ρ).symm⟩
  bobChannel := ⟨1, _, by convert (g64g_perm (fun o : Qubits 0 × (Qubits 0 × Qubits 1) =>
      ((), ((), ((default : Qubits 0), (o.2.2, (default : Qubits 0)))))) g64g_bob_bij).1,
    fun ρ => ((g64g_perm (fun o : Qubits 0 × (Qubits 0 × Qubits 1) =>
      ((), ((), ((default : Qubits 0), (o.2.2, (default : Qubits 0)))))) g64g_bob_bij).2 ρ).symm⟩

theorem solution :
    ExactConversion emptyResource 0 1 0 (taskTarget 0 0 1) := by
  refine ⟨g64g_P, rfl, rfl, rfl, ?_⟩
  funext M
  ext i j
  simp only [aliceMap, idTensorSuperop, transmittedCodeState, g64g_P, g64g_enc, g64g_ali, g64g_bob,
    Matrix.of_apply, initialCodeState, emptyResource, forwardResource, taskTarget]
  simp [g64g_psi, pureDensity, maxEntangled, emptySource, Matrix.of_apply, g64g_bit_inj, g64g_c_eq]
  erw [Matrix.of_apply, Matrix.of_apply]
  simp [g64g_bit_inj]
  have e1 : ∀ x y : Qubits 0, (x = y) = True := fun x y => eq_true (Subsingleton.elim x y)
  have hM : ∀ a b : TaskInput 0 0, M a b = M (i.2.1, i.2.2.1) (j.2.1, j.2.2.1) := fun a b => by
    congr 1 <;> exact Subsingleton.elim _ _
  simp only [e1, if_true]
  split_ifs <;> (try rw [hM]) <;> ring

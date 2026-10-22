-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P04.capacityOrdering
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:03:42.468894+00:00
-- url     : https://prove2.me/submissions/1c30dbd7-4b17-4e3d-9d41-ed350d87d81e

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04
open QAlgorithms.Papers.Independent.Gap48.P04
open QAlgorithms

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)


theorem g73k_pd_ket {ι : Type*} [DecidableEq ι] (c : ι) :
    pureDensity (ket c) = Matrix.single c c (1 : ℂ) := by
  ext a b
  simp only [pureDensity, ket, Matrix.of_apply, Matrix.single_apply]
  by_cases ha : a = c <;> by_cases hb : b = c <;> simp [ha, hb] <;> tauto

theorem g73k_single_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι) :
    (Matrix.single c c (1 : ℂ)).PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self (Matrix.single c c (1:ℂ))
  simpa [Matrix.single_mul_single_same] using this

theorem g73k_ket_state {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι) : IsState (ket c) := by
  simp [IsState, ket]

theorem g73k_kraus_density {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {m : ℕ}
    (K : Fin m → Matrix κ ι ℂ) (hK : IsKrausFamily K) (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (krausApply K ρ) := by
  refine ⟨?_, ?_⟩
  · unfold krausApply
    exact Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (K j)
  · unfold krausApply
    rw [Matrix.trace_sum]
    have : ∀ j, (K j * ρ * (K j)ᴴ).trace = ((K j)ᴴ * K j * ρ).trace := by
      intro j; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun j _ => this j, ← Matrix.trace_sum, ← Finset.sum_mul, hK,
      Matrix.one_mul]
    exact hρ.2

theorem g73k_QleC {d e : ℕ} (N : Superop (Fin d) (Fin e)) (R : ℝ) (h : QuantumSupported N R) :
    ClassicalSupported N R := by
  intro eta heta
  obtain ⟨m, n, hn, hR, P, hP⟩ := h (eta / 2) (by positivity)
  obtain ⟨k, K, hK, hKd⟩ := P.decode_channel
  obtain ⟨k', K', hK', hKe⟩ := P.encode_channel
  have hpovm : IsPOVM (fun x : Qubits m => ∑ j, (K j)ᴴ * Matrix.single x x (1:ℂ) * K j) := by
    refine ⟨fun x => ?_, ?_⟩
    · exact Matrix.posSemidef_sum _ fun j _ =>
        (g73k_single_psd x).conjTranspose_mul_mul_same (K j)
    · rw [Finset.sum_comm]
      have e : ∀ j, ∑ x : Qubits m, (K j)ᴴ * Matrix.single x x (1:ℂ) * K j =
          (K j)ᴴ * (∑ x : Qubits m, Matrix.single x x (1:ℂ)) * K j := by
        intro j; rw [Matrix.mul_sum, Matrix.sum_mul]
      rw [Finset.sum_congr rfl fun j _ => e j]
      have : ∑ x : Qubits m, Matrix.single x x (1:ℂ) = 1 := by
        ext a b
        rw [Matrix.sum_apply]
        simp only [Matrix.single_apply, Matrix.one_apply]
        by_cases hab : a = b
        · subst hab; simp
        · simp [hab]
      simp_rw [this, Matrix.mul_one]; exact hK
  have hdens : ∀ x : Qubits m, IsDensityMatrix (P.encode (Matrix.single x x (1:ℂ))) := by
    intro x
    rw [hKe]; apply g73k_kraus_density K' hK'
    exact ⟨g73k_single_psd x, by simp⟩
  refine ⟨m, n, hn, hR, ⟨fun x => P.encode (Matrix.single x x 1), hdens,
    fun x => ∑ j, (K j)ᴴ * Matrix.single x x (1:ℂ) * K j, hpovm⟩, fun x => ?_⟩
  have h1 := hP (ket x) (g73k_ket_state x)
  simp only [UnknownQubitCode.output, Function.comp, g73k_pd_ket] at h1
  have h2 : effectProb (∑ j, (K j)ᴴ * Matrix.single x x (1:ℂ) * K j)
      (piSuperop (fun _ : Fin n => N) (P.encode (Matrix.single x x 1))) =
      effectProb (Matrix.single x x 1)
        (P.decode (piSuperop (fun _ : Fin n => N) (P.encode (Matrix.single x x 1)))) := by
    rw [hKd]
    unfold effectProb krausApply
    congr 1
    rw [Finset.sum_mul, Matrix.trace_sum, Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  show 1 - effectProb _ _ < eta
  rw [h2]; linarith


def g73k_memA (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => g73k_memA d k * d

def g73k_memB (e : ℕ) : ℕ → ℕ → ℕ
  | 0, b => b
  | k+1, b => g73k_memB e k (e*b)

def g73k_alpha (d : ℕ) : (k : ℕ) → Fin (g73k_memA d k) ≃ (Fin k → Fin d)
  | 0 => Equiv.ofUnique (Fin 1) (Fin 0 → Fin d)
  | k+1 => (finProdFinEquiv (m := g73k_memA d k) (n := d)).symm.trans
      ((Equiv.prodComm _ _).trans (((Equiv.refl (Fin d)).prodCongr (g73k_alpha d k)).trans
        (Fin.consEquiv (fun _ => Fin d))))

def g73k_beta (e : ℕ) : (k b : ℕ) → Fin (g73k_memB e k b) ≃ (Fin k → Fin e) × Fin b
  | 0, b => (Equiv.uniqueProd (Fin b) (Fin 0 → Fin e)).symm
  | k+1, b => (g73k_beta e k (e*b)).trans
      (((Equiv.refl _).prodCongr (finProdFinEquiv (m := e) (n := b)).symm).trans
        ((Equiv.prodAssoc _ _ _).symm.trans
          (((Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => Fin e))).prodCongr (Equiv.refl _))))

theorem g73k_alpha_succ (d k : ℕ) (p : Fin (g73k_memA d k)) (i : Fin d) :
    g73k_alpha d (k+1) (finProdFinEquiv (p, i)) = Fin.cons i (g73k_alpha d k p) := by
  show (Fin.consEquiv (fun _ : Fin (k+1) => Fin d)) (((Equiv.refl _).prodCongr (g73k_alpha d k))
    ((Equiv.prodComm _ _) (finProdFinEquiv.symm (finProdFinEquiv (p,i))))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem g73k_beta_succ (e k b : ℕ) (u : Fin (g73k_memB e (k+1) b)) :
    g73k_beta e (k+1) b u =
      (Fin.cons (finProdFinEquiv.symm (g73k_beta e k (e*b) u).2).1 (g73k_beta e k (e*b) u).1,
        (finProdFinEquiv.symm (g73k_beta e k (e*b) u).2).2) := by
  rfl

theorem g73k_sum_fpf (d k : ℕ) (f : Fin (g73k_memA d (k+1)) → ℂ) :
    ∑ P, f P = ∑ q : Fin (g73k_memA d k), ∑ i : Fin d,
      f (finProdFinEquiv (q, i) : Fin (g73k_memA d k * d)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)).symm

theorem g73k_mul3 (a b c : ℂ) : a * b * c = (b * c) * a := by ring

/-- iterated send semantics -/
def g73k_Psi {d e : ℕ} : (k b : ℕ) → Schedule d e k →
    Superop (Fin (g73k_memA d k) × Fin b) (Fin (g73k_memB e k b))
  | 0, _, _, X => traceLeft X
  | k+1, b, S, X => g73k_Psi k (e*b) (fun i => S i.succ) (sendRegister (S 0) X)

theorem g73k_valid {d e m : ℕ} : ∀ (k b : ℕ) (F : Superop (Fin (g73k_memB e k b)) (Qubits m)),
    IsChannel F → Adaptive d e m (fun S X => F (g73k_Psi (d := d) k b S X))
  | 0, b, F, hF => Adaptive.finish (a := 1) F hF
  | k+1, b, F, hF => Adaptive.send (a := g73k_memA d k) (b := b)
      (fun S X => F (g73k_Psi (d := d) k (e*b) S X)) (g73k_valid k (e*b) F hF)

def g73k_Nsing {d e : ℕ} (N : Superop (Fin d) (Fin e)) (i j : Fin d) (y y' : Fin e) : ℂ :=
  N (Matrix.single i j 1) y y'

theorem g73k_lin {d e : ℕ} (N : Superop (Fin d) (Fin e)) (hN : IsChannel N)
    (M : Matrix (Fin d) (Fin d) ℂ) (y y' : Fin e) :
    N M y y' = ∑ i, ∑ j, M i j * g73k_Nsing N i j y y' := by
  obtain ⟨l, K, -, hK⟩ := hN
  simp only [g73k_Nsing, hK, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (γ := Fin l)]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (γ := Fin l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ite_and]
  simp [mul_comm, mul_assoc]

theorem g73k_Psi_formula {d e : ℕ} (N : Superop (Fin d) (Fin e)) (hN : IsChannel N) :
    ∀ (k b : ℕ) (X : Matrix (Fin (g73k_memA d k) × Fin b) (Fin (g73k_memA d k) × Fin b) ℂ) (u u' : Fin (g73k_memB e k b)),
    g73k_Psi k b (fun _ => N) X u u' =
      ∑ p : Fin (g73k_memA d k), ∑ p' : Fin (g73k_memA d k),
        X (p, (g73k_beta e k b u).2) (p', (g73k_beta e k b u').2) *
          ∏ i, g73k_Nsing N (g73k_alpha d k p i) (g73k_alpha d k p' i)
            ((g73k_beta e k b u).1 i) ((g73k_beta e k b u').1 i)
  | 0, b, X, u, u' => by
    change ∑ a : Fin 1, X (a,u) (a,u') = ∑ p : Fin 1, ∑ p' : Fin 1, X (p, u) (p', u') * ∏ i : Fin 0, _
    simp
  | k+1, b, X, u, u' => by
    change g73k_Psi k (e*b) (fun _ => N) (sendRegister N X) u u' = _
    rw [g73k_Psi_formula N hN k (e*b) _ u u']
    simp only [sendRegister]
    simp only [g73k_sum_fpf d k, g73k_alpha_succ, g73k_beta_succ, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    generalize g73k_beta e k (e * b) u = w
    generalize g73k_beta e k (e * b) u' = w'
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q' _ => ?_
    refine Eq.trans (congrArg (fun z => z * _) (g73k_lin N hN _ _ _)) ?_
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    exact mul_assoc _ _ _

theorem g73k_memA_pos (d : ℕ) (hd : 0 < d) : ∀ k, 0 < g73k_memA d k
  | 0 => Nat.one_pos
  | k+1 => Nat.mul_pos (g73k_memA_pos d hd k) hd

theorem g73k_sub_sum {α β : Type*} {l : ℕ} (M : Fin l → Matrix α α ℂ) (f g : β → α) :
    ∑ j, (M j).submatrix f g = (∑ j, M j).submatrix f g := by
  ext a b; simp [Matrix.sum_apply]

theorem g73k_chan_pre {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq ι]
    [DecidableEq ι'] (Φ : Superop ι κ) (hΦ : IsChannel Φ) (σ : ι ≃ ι') :
    IsChannel (fun Z : Matrix ι' ι' ℂ => Φ (Z.submatrix σ σ)) := by
  obtain ⟨l, K, hK, hKe⟩ := hΦ
  refine ⟨l, fun j => (K j).submatrix id σ.symm, ?_, fun Z => ?_⟩
  · unfold IsKrausFamily at hK ⊢
    have : ∀ j, ((K j).submatrix id σ.symm)ᴴ * (K j).submatrix id σ.symm =
        ((K j)ᴴ * K j).submatrix σ.symm σ.symm := by
      intro j
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    simp_rw [this]
    rw [g73k_sub_sum, hK, Matrix.submatrix_one_equiv]
  · show Φ (Z.submatrix σ σ) = _
    rw [hKe]
    unfold krausApply
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (K j).submatrix id σ.symm = (K j).submatrix id σ.symm := rfl
    ext a b
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    refine Fintype.sum_equiv σ _ _ (fun c => ?_)
    rw [σ.symm_apply_apply]
    congr 1
    exact Fintype.sum_equiv σ _ _ (fun c' => by simp)

theorem g73k_chan_post {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ'] [DecidableEq ι]
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) (τ : κ' ≃ κ) :
    IsChannel (fun Z => (Φ Z).submatrix τ τ) := by
  obtain ⟨l, K, hK, hKe⟩ := hΦ
  refine ⟨l, fun j => (K j).submatrix τ id, ?_, fun Z => ?_⟩
  · unfold IsKrausFamily at hK ⊢
    have : ∀ j, ((K j).submatrix τ id)ᴴ * (K j).submatrix τ id =
        ((K j)ᴴ * K j) := by
      intro j
      rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ τ.bijective,
        Matrix.submatrix_id_id]
    simp_rw [this]; exact hK
  · show (Φ Z).submatrix τ τ = _
    rw [hKe]
    unfold krausApply
    rw [← g73k_sub_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext a b
    simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

theorem g73k_QleQ2 {d e : ℕ} (hd : 0 < d) (N : Superop (Fin d) (Fin e)) (hN : IsChannel N)
    (R : ℝ) (h : QuantumSupported N R) : TwoWaySupported N R := by
  intro eta heta
  obtain ⟨m, n, hn, hR, P, hP⟩ := h eta heta
  let γ : (Fin n → Fin e) ≃ Fin (g73k_memB e n 1) :=
    (Equiv.prodUnique (Fin n → Fin e) (Fin 1)).symm.trans (g73k_beta e n 1).symm
  let F : Superop (Fin (g73k_memB e n 1)) (Qubits m) := fun Z => P.decode (Z.submatrix γ γ)
  have hF : IsChannel F := g73k_chan_pre P.decode P.decode_channel γ
  let P' : TwoWayQubitCode d e n m :=
    { memory := g73k_memA d n
      memory_positive := g73k_memA_pos d hd n
      encode := fun ρ => (P.encode ρ).submatrix (g73k_alpha d n) (g73k_alpha d n)
      encode_channel := g73k_chan_post P.encode P.encode_channel (g73k_alpha d n)
      run := fun S X => F (g73k_Psi (d := d) n 1 S X)
      valid := g73k_valid n 1 F hF }
  refine ⟨m, n, hn, hR, P', fun psi hpsi => ?_⟩
  have hout : P'.output (fun _ => N) (pureDensity psi) = P.output N (pureDensity psi) := by
    show P.decode (Matrix.submatrix (g73k_Psi n 1 (fun _ => N) _) γ γ) = _
    simp only [UnknownQubitCode.output, Function.comp]
    congr 1
    ext z z'
    rw [Matrix.submatrix_apply, g73k_Psi_formula N hN]
    have hb : ∀ z, g73k_beta e n 1 (γ z) = (z, 0) := by
      intro z; simp [γ]
    simp only [hb, Matrix.kronecker_apply, Matrix.submatrix_apply, Matrix.one_apply_eq, mul_one,
      piSuperop, Matrix.of_apply, g73k_Nsing]
    rw [← (g73k_alpha d n).symm.sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← (g73k_alpha d n).symm.sum_comp]
    simp [P']
  rw [hout]; exact hP psi hpsi

/-- Bennett--DiVincenzo--Smolin, PDF p.2: Q <= Q2 and Q <= C for every
finite-dimensional CPTP channel. No ordering between Q2 and C is asserted. -/
theorem solution (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (N : Superop (Fin d) (Fin e)) (hN : IsChannel N) :
    uniformQuantumCapacity N ≤ adaptiveQuantumCapacity N ∧ uniformQuantumCapacity N ≤ worstMessageCapacity N := by
  unfold uniformQuantumCapacity adaptiveQuantumCapacity worstMessageCapacity
  constructor
  · apply sSup_le
    rintro q ⟨R, hR0, hRs, rfl⟩
    exact le_sSup ⟨R, hR0, g73k_QleQ2 hd N hN R hRs, rfl⟩
  · apply sSup_le
    rintro q ⟨R, hR0, hRs, rfl⟩
    exact le_sSup ⟨R, hR0, g73k_QleC N R hRs, rfl⟩

end


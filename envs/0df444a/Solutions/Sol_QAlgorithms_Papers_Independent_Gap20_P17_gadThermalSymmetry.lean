-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P17.gadThermalSymmetry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:18:04.718796+00:00
-- url     : https://prove2.me/submissions/7272ceb6-af91-4f1f-a840-2e4fd38935db

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma g73h_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

def g73h_ptr {Z X Y : Type*} [Fintype Y] (e : Z ≃ X × Y) (M : Matrix Z Z ℂ) : Matrix X X ℂ :=
  fun a b => ∑ r, M (e.symm (a, r)) (e.symm (b, r))

lemma g73h_ptr_conj {Z X Y : Type*} [Fintype Z] [Fintype X] [Fintype Y] [DecidableEq Y]
    (e : Z ≃ X × Y) (M W : Matrix Z Z ℂ) (A : Matrix X X ℂ) (B : Matrix Y Y ℂ)
    (hB : Bᴴ * B = 1)
    (hW : ∀ a r p t, W (e.symm (a, r)) (e.symm (p, t)) = A a p * B r t) :
    g73h_ptr e (W * M * Wᴴ) = A * g73h_ptr e M * Aᴴ := by
  have h1 : ∀ f : Z → ℂ, ∑ z, f z = ∑ p, ∑ t, f (e.symm (p, t)) := fun f => by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hB' : ∀ t t', ∑ r, star (B r t') * B r t = if t' = t then 1 else 0 := by
    intro t t'
    have := congrFun (congrFun hB t') t
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  ext a b
  simp only [g73h_ptr, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [h1 (fun z => _ * star _), h1 (fun z => W _ z * M z _), hW]
  simp only [star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  calc _ = ∑ r, ∑ p, ∑ t, ∑ t', A a p * B r t * M (e.symm (p, t)) (e.symm (q, t')) *
        (star (A b q) * star (B r t')) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ p, ∑ t, ∑ t', ∑ r, A a p * B r t * M (e.symm (p, t)) (e.symm (q, t')) *
        (star (A b q) * star (B r t')) := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun t _ => ?_
        have : ∀ t', ∑ r, A a p * B r t * M (e.symm (p, t)) (e.symm (q, t')) *
            (star (A b q) * star (B r t')) = A a p * M (e.symm (p, t)) (e.symm (q, t')) *
            star (A b q) * (∑ r, star (B r t') * B r t) := by
          intro t'; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; ring
        simp_rw [this, hB']
        simp

lemma g73h_ptr_herm {Z X Y : Type*} [Fintype Y] (e : Z ≃ X × Y) (M : Matrix Z Z ℂ)
    (hM : M.IsHermitian) : (g73h_ptr e M).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, g73h_ptr, star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Matrix.conjTranspose_apply, hM]

lemma g73h_conj_pow {X : Type*} [Fintype X] [DecidableEq X] (A M : Matrix X X ℂ)
    (hA : Aᴴ * A = 1) (k : ℕ) : (A * M * Aᴴ) ^ (k + 1) = A * M ^ (k + 1) * Aᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc A * M ^ (k + 1) * Aᴴ * (A * M * Aᴴ) = A * M ^ (k + 1) * (Aᴴ * A) * M * Aᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA, Matrix.mul_one, pow_succ M (k + 1)]; simp only [Matrix.mul_assoc]

lemma g73h_entropy_conj {X : Type*} [Fintype X] {_ : DecidableEq X} (A M : Matrix X X ℂ)
    (hA : Aᴴ * A = 1) (hM : M.IsHermitian) : vnEntropy (A * M * Aᴴ) = vnEntropy M := by
  unfold vnEntropy
  have hH : (A * M * Aᴴ).IsHermitian := by
    exact Matrix.isHermitian_mul_mul_conjTranspose A hM
  rw [g73h_trace_cfc_eq _ _ hH hM _ (by simp)]
  intro k
  rw [g73h_conj_pow A M hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, Matrix.one_mul]

def g73h_X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def g73h_P : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
def g73h_W : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ := fun be be' => g73h_X be.1 be'.1 * g73h_P be.2 be'.2

lemma g73h_X_ct : g73h_Xᴴ = g73h_X := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [g73h_X]

lemma g73h_XX : g73h_X * g73h_X = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [g73h_X, Matrix.mul_apply, Fin.sum_univ_two]

lemma g73h_XctX : g73h_Xᴴ * g73h_X = 1 := by rw [g73h_X_ct, g73h_XX]

lemma g73h_PctP : g73h_Pᴴ * g73h_P = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [g73h_P, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]

lemma g73h_D (eta alpha : ℝ) :
    gadDilation eta (1-alpha) = g73h_W * gadDilation eta alpha * g73h_X := by
  have h : (1 - (1 - alpha)) = alpha := by ring
  ext ⟨b, e⟩ a
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases b <;> fin_cases e <;> fin_cases a <;>
    simp [gadDilation, gadKraus, adKraus, g73h_W, g73h_X, g73h_P, h, Matrix.mul_apply,
      Fin.sum_univ_two]

lemma g73h_ptr_right (M : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ) :
    traceRight M = g73h_ptr (Equiv.refl _) M := by
  ext a b; rfl

lemma g73h_ptr_left (M : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ) :
    traceLeft M = g73h_ptr (Equiv.prodComm (Fin 4) (Fin 2)).symm M := by
  ext a b; rfl

lemma g73h_conj_out (V : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    (g73h_W * V * g73h_X) * (g73h_X * rho * g73h_X) * (g73h_W * V * g73h_X)ᴴ =
      g73h_W * (V * rho * Vᴴ) * g73h_Wᴴ := by
  have h1 : (g73h_W * V * g73h_X)ᴴ = g73h_X * Vᴴ * g73h_Wᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, g73h_X_ct, Matrix.mul_assoc]
  rw [h1]
  calc g73h_W * V * g73h_X * (g73h_X * rho * g73h_X) * (g73h_X * Vᴴ * g73h_Wᴴ)
      = g73h_W * V * (g73h_X * g73h_X) * rho * (g73h_X * g73h_X) * Vᴴ * g73h_Wᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [g73h_XX]; simp only [Matrix.mul_one, Matrix.mul_assoc]

lemma g73h_info (eta alpha : ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) (hrho : rho.IsHermitian) :
    forwardInfo (gadDilation eta (1-alpha)) (g73h_X * rho * g73h_X) =
      forwardInfo (gadDilation eta alpha) rho ∧
    reverseInfo (gadDilation eta (1-alpha)) (g73h_X * rho * g73h_X) =
      reverseInfo (gadDilation eta alpha) rho := by
  set V := gadDilation eta alpha
  have hM : (V * rho * Vᴴ).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V hrho
  have hR : receiverChannel (gadDilation eta (1-alpha)) (g73h_X * rho * g73h_X) =
      g73h_X * receiverChannel V rho * g73h_Xᴴ := by
    simp only [receiverChannel]
    rw [g73h_D, g73h_conj_out, g73h_ptr_right, g73h_ptr_right]
    exact g73h_ptr_conj (Equiv.refl _) _ g73h_W g73h_X g73h_P g73h_PctP (fun _ _ _ _ => rfl)
  have hE : complementaryChannel (gadDilation eta (1-alpha)) (g73h_X * rho * g73h_X) =
      g73h_P * complementaryChannel V rho * g73h_Pᴴ := by
    simp only [complementaryChannel]
    rw [g73h_D, g73h_conj_out, g73h_ptr_left, g73h_ptr_left]
    exact g73h_ptr_conj _ _ g73h_W g73h_P g73h_X g73h_XctX (fun _ _ _ _ => by
      simp [g73h_W, mul_comm])
  have hRh : (receiverChannel V rho).IsHermitian := by
    simp only [receiverChannel]; rw [g73h_ptr_right]; exact g73h_ptr_herm _ _ hM
  have hEh : (complementaryChannel V rho).IsHermitian := by
    simp only [complementaryChannel]; rw [g73h_ptr_left]; exact g73h_ptr_herm _ _ hM
  have hS : vnEntropy (g73h_X * rho * g73h_X) = vnEntropy rho := by
    have := g73h_entropy_conj g73h_X rho g73h_XctX hrho
    rwa [g73h_X_ct] at this
  refine ⟨?_, ?_⟩
  · simp only [forwardInfo]
    rw [hR, hE, g73h_entropy_conj _ _ g73h_XctX hRh, g73h_entropy_conj _ _ g73h_PctP hEh]
  · simp only [reverseInfo]
    rw [hE, hS, g73h_entropy_conj _ _ g73h_PctP hEh]

lemma g73h_dens (rho : Matrix (Fin 2) (Fin 2) ℂ) (h : IsDensityMatrix rho) :
    IsDensityMatrix (g73h_X * rho * g73h_X) := by
  refine ⟨?_, ?_⟩
  · have := h.1.mul_mul_conjTranspose_same g73h_X
    rwa [g73h_X_ct] at this
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, g73h_XX, Matrix.one_mul]; exact h.2

lemma g73h_back (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    g73h_X * (g73h_X * rho * g73h_X) * g73h_X = rho := by
  calc _ = (g73h_X * g73h_X) * rho * (g73h_X * g73h_X) := by simp only [Matrix.mul_assoc]
    _ = rho := by rw [g73h_XX]; simp

lemma g73h_fmax (eta alpha : ℝ) :
    forwardMaximum (gadDilation eta alpha) = forwardMaximum (gadDilation eta (1-alpha)) := by
  unfold forwardMaximum
  congr 1
  ext r
  constructor
  · rintro ⟨rho, hd, rfl⟩
    exact ⟨_, g73h_dens rho hd, ((g73h_info eta alpha rho hd.1.1).1).symm⟩
  · rintro ⟨rho, hd, rfl⟩
    refine ⟨_, g73h_dens rho hd, ?_⟩
    have := (g73h_info eta alpha (g73h_X * rho * g73h_X) (g73h_dens rho hd).1.1).1
    rw [g73h_back] at this
    exact this

lemma g73h_rmax (eta alpha : ℝ) :
    reverseMaximum (gadDilation eta alpha) = reverseMaximum (gadDilation eta (1-alpha)) := by
  unfold reverseMaximum
  congr 1
  ext r
  constructor
  · rintro ⟨rho, hd, rfl⟩
    exact ⟨_, g73h_dens rho hd, ((g73h_info eta alpha rho hd.1.1).2).symm⟩
  · rintro ⟨rho, hd, rfl⟩
    refine ⟨_, g73h_dens rho hd, ?_⟩
    have := (g73h_info eta alpha (g73h_X * rho * g73h_X) (g73h_dens rho hd).1.1).2
    rw [g73h_back] at this
    exact this

lemma g73h_diag (p : ℝ) : g73h_X * diagonalInput p * g73h_X = diagonalInput (1-p) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [g73h_X, diagonalInput]

lemma g73h_diag_herm (p : ℝ) : (diagonalInput p).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalInput]

lemma g73h_channel (eta alpha : ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    gadChannel eta (1-alpha) rho = g73h_X * gadChannel eta alpha (g73h_X*rho*g73h_X) * g73h_X := by
  have h : (1 - (1 - alpha)) = alpha := by ring
  ext i j
  simp only [gadChannel, QAlgorithms.krausApply, Fin.sum_univ_four, Matrix.add_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [gadKraus, adKraus, g73h_X, h, Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_ofReal] <;>
    ring

/-- PDF pp.3–4: thermal reflection alpha↔1-alpha conjugates the channel by X,
preserves both optimized entropy quantities, and reflects every optimal diagonal
population p to 1-p. The physical mixture weights correct the p.3 typo. -/
theorem solution (eta alpha : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (halpha : alpha ∈ Set.Icc (0 : ℝ) 1) :
    (let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
     ∀ rho : Matrix (Fin 2) (Fin 2) ℂ,
       gadChannel eta (1-alpha) rho = X * gadChannel eta alpha (X*rho*X) * X) ∧
    forwardMaximum (gadDilation eta alpha) = forwardMaximum (gadDilation eta (1-alpha)) ∧
    reverseMaximum (gadDilation eta alpha) = reverseMaximum (gadDilation eta (1-alpha)) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1,
      (forwardInfo (gadDilation eta alpha) (diagonalInput p) =
        forwardMaximum (gadDilation eta alpha) ↔
       forwardInfo (gadDilation eta (1-alpha)) (diagonalInput (1-p)) =
        forwardMaximum (gadDilation eta (1-alpha))) ∧
      (reverseInfo (gadDilation eta alpha) (diagonalInput p) =
        reverseMaximum (gadDilation eta alpha) ↔
       reverseInfo (gadDilation eta (1-alpha)) (diagonalInput (1-p)) =
        reverseMaximum (gadDilation eta (1-alpha)))) := by
  refine ⟨?_, g73h_fmax eta alpha, g73h_rmax eta alpha, ?_⟩
  · intro X rho
    exact g73h_channel eta alpha rho
  · intro p _
    have e1 := g73h_info eta alpha (diagonalInput p) (g73h_diag_herm p)
    rw [g73h_diag] at e1
    rw [e1.1, e1.2, g73h_fmax, g73h_rmax]
    exact ⟨Iff.rfl, Iff.rfl⟩



end

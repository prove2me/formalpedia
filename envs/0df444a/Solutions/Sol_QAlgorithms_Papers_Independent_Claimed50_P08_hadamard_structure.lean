-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P08.hadamard_structure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:34:07.002835+00:00
-- url     : https://prove2.me/submissions/5b1ac5bc-a7e5-437c-a022-f3e38b3b1bb2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08
noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Claimed50.P08
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50

theorem g58c_unit {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) (h : ‖v‖ = 1) :
    ∑ k, star (v k) * v k = 1 := by
  have h2 : ∑ k, ‖v k‖ ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq v
    rw [h] at this
    have h0 : 0 ≤ ∑ k, ‖v k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    nlinarith [Real.sq_sqrt h0]
  have : ∀ k, star (v k) * v k = ((‖v k‖ ^ 2 : ℝ) : ℂ) := by
    intro k; rw [RCLike.star_def, Complex.conj_mul']; push_cast; rfl
  simp_rw [this]; rw [← Complex.ofReal_sum, h2]; simp

theorem g58c_chan {ι κ K : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype K]
    (Φ : Superop ι κ) (E : K → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1)
    (hΦ : ∀ ρ, Φ ρ = ∑ k, E k * ρ * (E k)ᴴ) : IsChannel Φ := by
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (e.symm j), ?_, ?_⟩
  · unfold IsKrausFamily; rw [← hE]; exact e.symm.sum_comp (fun k => (E k)ᴴ * E k)
  · intro ρ; rw [hΦ]; unfold krausApply
    exact (e.symm.sum_comp (fun k => E k * ρ * (E k)ᴴ)).symm

theorem g58c_povm {a b c : ℕ} (H : HadamardData a b c) (i j : BroadcastRegister a) :
    ∑ x, H.phi x i * conj (H.phi x j) = if i = j then 1 else 0 := by
  have := congrFun (congrFun H.povm i) j
  simpa [pureDensity, Matrix.sum_apply, Matrix.one_apply] using this

theorem g58c_iso {a b c : ℕ} (H : HadamardData a b c) :
    (inputIsometry H)ᴴ * inputIsometry H = 1 := by
  ext i j
  rw [Matrix.one_apply, ← g58c_povm H i j]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inputIsometry, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hu := g58c_unit (H.psi x) (H.unit x)
  calc ∑ k, star (H.psi x k * conj (H.phi x i)) * (H.psi x k * conj (H.phi x j))
      = (∑ k, star (H.psi x k) * H.psi x k) * (H.phi x i * conj (H.phi x j)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [star_mul', RCLike.star_def, Complex.conj_conj]; ring
    _ = _ := by rw [hu, one_mul]

theorem g58c_entry {a b c : ℕ} (H : HadamardData a b c) (sigma : Op (BroadcastRegister a))
    (p q : BroadcastRegister b × BroadcastRegister c) :
    hadamardChannel H sigma p q =
      inputCoefficient H sigma p.1 q.1 * H.psi p.1 p.2 * conj (H.psi q.1 q.2) := by
  simp only [hadamardChannel, conjSuperop, inputCoefficient, Matrix.mul_apply,
    Matrix.conjTranspose_apply, inputIsometry, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [star_mul', RCLike.star_def, Complex.conj_conj]; ring

theorem g58c_chanH {a b c : ℕ} (H : HadamardData a b c) : IsChannel (hadamardChannel H) :=
  g58c_chan _ (fun _ : Unit => inputIsometry H) (by simpa using g58c_iso H)
    (fun ρ => by simp [hadamardChannel, conjSuperop])

theorem g58c_P {a b c : ℕ} (H : HadamardData a b c) :
    let P := 1 - inputIsometry H * (inputIsometry H)ᴴ
    Pᴴ * P = P := by
  intro P
  have hU := g58c_iso H
  have hPh : Pᴴ = P := by simp [P, Matrix.conjTranspose_sub]
  rw [hPh]
  simp only [P]
  have : inputIsometry H * (inputIsometry H)ᴴ * (inputIsometry H * (inputIsometry H)ᴴ) =
      inputIsometry H * (inputIsometry H)ᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (inputIsometry H)ᴴ, hU, Matrix.one_mul]
  rw [sub_mul, mul_sub, mul_sub, this]; simp

theorem g58c_pd0 {a : ℕ} :
    pureDensity (ket (0 : BroadcastRegister a)) = Matrix.single 0 0 1 := by
  ext i j
  simp [pureDensity, ket, Matrix.single_apply]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, eq_comm]

theorem g58c_chanR {a b c : ℕ} (H : HadamardData a b c) : IsChannel (isometricRecovery H) := by
  set U := inputIsometry H
  set P := 1 - U * Uᴴ with hP
  have hPP : Pᴴ * P = P := g58c_P H
  let S : BroadcastRegister b × BroadcastRegister c →
      Matrix (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c) ℂ :=
    fun k => Matrix.single 0 k 1
  have hS : ∀ k, (S k)ᴴ = Matrix.single k 0 1 := by
    intro k; simp [S, Matrix.conjTranspose_single]
  let E : Option (BroadcastRegister b × BroadcastRegister c) →
      Matrix (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c) ℂ :=
    fun o => match o with
      | none => Uᴴ
      | some k => S k * P
  refine g58c_chan _ E ?_ ?_
  · rw [Fintype.sum_option]
    have h1 : ∀ k : BroadcastRegister b × BroadcastRegister c,
        (E (some k))ᴴ * E (some k) = Pᴴ * Matrix.single k k (1 : ℂ) * P := by
      intro k
      simp only [E, Matrix.conjTranspose_mul, hS]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single k 0 1), Matrix.single_mul_single_same,
        one_mul, Matrix.mul_assoc]
    simp_rw [h1, ← Finset.sum_mul, ← Finset.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
    simp only [E, Matrix.conjTranspose_conjTranspose]
    rw [hPP, hP]; abel
  · intro ρ
    rw [Fintype.sum_option]
    have h1 : ∀ k : BroadcastRegister b × BroadcastRegister c,
        E (some k) * ρ * (E (some k))ᴴ =
          (P * ρ * Pᴴ) k k • (Matrix.single (0 : BroadcastRegister a) 0 (1 : ℂ)) := by
      intro k
      simp only [E, Matrix.conjTranspose_mul, hS]
      have e : S k * P * ρ * (Pᴴ * Matrix.single k (0 : BroadcastRegister a) (1 : ℂ)) =
          (S k * (P * ρ * Pᴴ) : Matrix (BroadcastRegister a) _ ℂ) * Matrix.single k (0 : BroadcastRegister a) (1 : ℂ) := by
        simp only [Matrix.mul_assoc]
      rw [e]
      simp only [S]
      rw [Matrix.single_mul_mul_single, Matrix.smul_single]; simp
    simp_rw [h1, ← Finset.sum_smul]
    simp only [E, isometricRecovery, Matrix.conjTranspose_conjTranspose]
    rw [g58c_pd0]
    congr 2
    have : ∑ k, (P * ρ * Pᴴ) k k = (P * ρ * Pᴴ).trace := rfl
    rw [this, Matrix.trace_mul_comm (P * ρ), ← Matrix.mul_assoc, hPP, hP, sub_mul, Matrix.trace_sub, one_mul]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm (inputIsometry H)ᴴ, Matrix.mul_assoc,
      Matrix.trace_mul_comm ρ]

theorem g58c_recov {a b c : ℕ} (H : HadamardData a b c) :
    isometricRecovery H ∘ hadamardChannel H = id := by
  funext σ
  have hU := g58c_iso H
  simp only [Function.comp_apply, id, isometricRecovery, hadamardChannel, conjSuperop]
  have e : (inputIsometry H)ᴴ * (inputIsometry H * σ * (inputIsometry H)ᴴ) * inputIsometry H = σ := by
    simp only [← Matrix.mul_assoc]; rw [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]; simp

theorem g58c_bob {a b c : ℕ} (H : HadamardData a b c) (sigma : Op (BroadcastRegister a))
    (x y : BroadcastRegister b) :
    bobChannel H sigma x y = inputCoefficient H sigma x y * inner ℂ (H.psi y) (H.psi x) := by
  simp only [bobChannel, Function.comp_apply, traceRight, Matrix.of_apply, g58c_entry]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem g58c_charlie {a b c : ℕ} (H : HadamardData a b c) (sigma : Op (BroadcastRegister a)) :
    charlieChannel H sigma = ∑ x, inputCoefficient H sigma x x • pureDensity (H.psi x) := by
  ext k k'
  simp only [charlieChannel, Function.comp_apply, traceLeft, Matrix.of_apply, g58c_entry,
    Matrix.sum_apply, Matrix.smul_apply, pureDensity, smul_eq_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_); ring

theorem g58c_diso {a b c : ℕ} (H : HadamardData a b c) :
    (degradingIsometry H)ᴴ * degradingIsometry H = 1 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, degradingIsometry, Matrix.one_apply,
    Fintype.sum_prod_type]
  by_cases hxy : x = y
  · subst hxy
    rw [← g58c_unit (H.psi x) (H.unit x)]
    rw [Finset.sum_eq_single x (fun y1 _ hy => by
      refine Finset.sum_eq_zero (fun y2 _ => Finset.sum_eq_zero (fun k _ => ?_)); simp [hy])
      (by simp)]
    rw [Finset.sum_eq_single x (fun y2 _ hy => Finset.sum_eq_zero (fun k _ => by simp [hy]))
      (by simp)]
    simp
  · simp only [hxy, if_false]
    refine Finset.sum_eq_zero (fun y1 _ => Finset.sum_eq_zero (fun y2 _ => Finset.sum_eq_zero
      (fun k _ => ?_)))
    by_cases h1 : y1 = x
    · subst h1; simp [hxy]
    · simp [h1]

theorem g58c_chanB {b : ℕ} : IsChannel (basisMeasurement (b := b)) := by
  refine g58c_chan _ (fun x : BroadcastRegister b => Matrix.single x x (1 : ℂ)) ?_ ?_
  · simp [Matrix.conjTranspose_single, Matrix.sum_single_one]
  · intro ρ
    simp only [basisMeasurement, Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single,
      one_mul, mul_one]
    rw [Matrix.sum_single_eq_diagonal]

theorem g58c_chanP {a b c : ℕ} (H : HadamardData a b c) : IsChannel (hadamardPreparation H) := by
  refine g58c_chan _ (fun x : BroadcastRegister b =>
    (Matrix.of fun k y => if y = x then H.psi x k else 0 :
      Matrix (BroadcastRegister c) (BroadcastRegister b) ℂ)) ?_ ?_
  · ext y y'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply]
    by_cases h : y = y'
    · subst h
      rw [Finset.sum_eq_single y (fun x _ hx => Finset.sum_eq_zero (fun k _ => by
        simp [Ne.symm hx])) (by simp)]
      simpa using g58c_unit (H.psi y) (H.unit y)
    · simp only [h, if_false]
      refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun k _ => ?_))
      by_cases h1 : y = x
      · subst h1; simp [Ne.symm h]
      · simp [h1]
  · intro ρ
    ext k k'
    simp only [hadamardPreparation, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.smul_apply, pureDensity, smul_eq_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp [Finset.sum_ite_eq', ite_mul, apply_ite (starRingEnd ℂ), mul_ite]
    ring

theorem g58c_prepB {a b c : ℕ} (H : HadamardData a b c) :
    hadamardPreparation H ∘ basisMeasurement = hadamardPreparation H := by
  funext ρ
  simp [hadamardPreparation, basisMeasurement]

theorem g58c_deg {a b c : ℕ} (H : HadamardData a b c) :
    degradingChannel H = hadamardPreparation H ∘ basisMeasurement := by
  rw [g58c_prepB]
  funext ρ
  ext k k'
  simp only [degradingChannel, Function.comp_apply, traceLeft, conjSuperop, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, degradingIsometry, hadamardPreparation,
    Matrix.sum_apply, Matrix.smul_apply, pureDensity, smul_eq_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single x]
      · simp; ring
      · intro y _ hy; simp [Ne.symm hy]
      · simp
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  · intro y _ hy
    refine Finset.sum_eq_zero (fun z _ => ?_)
    have : ∀ w, ¬ (x = w ∧ y = w) := fun w h => hy (h.2.trans h.1.symm)
    simp [this]
  · simp

theorem g58c_degB {a b c : ℕ} (H : HadamardData a b c) :
    degradingChannel H ∘ bobChannel H = charlieChannel H := by
  rw [g58c_deg, g58c_prepB]
  funext σ
  rw [g58c_charlie]
  simp only [Function.comp_apply, hadamardPreparation, g58c_bob]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have : inner ℂ (H.psi x) (H.psi x) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, H.unit x]; simp
  rw [this, mul_one]

/-- PDF pp.2–3, Section 2, (1)–(8): the Hadamard broadcast map is isometric
and reversible, both marginals have the displayed formulas, and Charlie is
simulated by Bob's explicit isometry or by basis measurement and hadamardPreparation.
The measurement input subscript below (7) is corrected from Y to B. -/
theorem solution {a b c : ℕ} (H : HadamardData a b c) :
    (inputIsometry H)ᴴ * inputIsometry H = 1 ∧
    IsChannel (hadamardChannel H) ∧
    (∀ (sigma : Op (BroadcastRegister a)) (p q : BroadcastRegister b × BroadcastRegister c),
      hadamardChannel H sigma p q =
        inputCoefficient H sigma p.1 q.1 * H.psi p.1 p.2 * conj (H.psi q.1 q.2)) ∧
    IsChannel (isometricRecovery H) ∧ isometricRecovery H ∘ hadamardChannel H = id ∧
    (∀ (sigma : Op (BroadcastRegister a)) (x y : BroadcastRegister b),
      bobChannel H sigma x y = inputCoefficient H sigma x y * inner ℂ (H.psi y) (H.psi x)) ∧
    (∀ sigma : Op (BroadcastRegister a), charlieChannel H sigma =
      ∑ x, inputCoefficient H sigma x x • pureDensity (H.psi x)) ∧
    (degradingIsometry H)ᴴ * degradingIsometry H = 1 ∧
    IsChannel (basisMeasurement (b := b)) ∧ IsChannel (hadamardPreparation H) ∧
    IsChannel (degradingChannel H) ∧
    degradingChannel H = hadamardPreparation H ∘ basisMeasurement ∧
    degradingChannel H ∘ bobChannel H = charlieChannel H := by
  refine ⟨g58c_iso H, g58c_chanH H, g58c_entry H, g58c_chanR H, g58c_recov H, g58c_bob H,
    g58c_charlie H, g58c_diso H, g58c_chanB, g58c_chanP H, ?_, g58c_deg H, g58c_degB H⟩
  rw [g58c_deg, g58c_prepB]; exact g58c_chanP H


end

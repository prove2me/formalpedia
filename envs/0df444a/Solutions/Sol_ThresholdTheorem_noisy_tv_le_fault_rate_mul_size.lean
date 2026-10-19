-- Prove2me | solution 1 for ThresholdTheorem.noisy_tv_le_fault_rate_mul_size
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T01:34:17.719995+00:00
-- url     : https://prove2.me/submissions/c23fb4db-0573-4b1c-9f9a-6f4061c711dd

import Definitions.Def_threshold_theorem_noise_model

open Matrix
open scoped ComplexOrder Kronecker
open ThresholdTheorem

private noncomputable def tvSplit {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) :
    (Q → Fin 2) ≃ ((Fin k → Fin 2) × ({q : Q // q ∉ Set.range s} → Fin 2)) := by
  classical
  apply Equiv.ofBijective (fun x => (x ∘ s, fun q => x q.1))
  constructor
  · intro x y h
    apply funext
    intro q
    by_cases hq : q ∈ Set.range s
    · obtain ⟨i, rfl⟩ := hq
      exact congrFun (congrArg Prod.fst h) i
    · exact congrFun (congrArg Prod.snd h) ⟨q, hq⟩
  · rintro ⟨a, b⟩
    refine ⟨fun q => if hq : q ∈ Set.range s then a (Classical.choose hq)
      else b ⟨q, hq⟩, ?_⟩
    apply Prod.ext
    · apply funext
      intro i
      dsimp
      rw [dif_pos ⟨i, rfl⟩]
      exact congrArg a (s.injective (Classical.choose_spec (show s i ∈ Set.range s from ⟨i, rfl⟩)))
    · ext q
      simp only [dif_neg q.2]

open Classical in
private lemma tv_lift_eq {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (A : QMat k) :
    liftOp s A = (A ⊗ₖ (1 : Matrix ({q : Q // q ∉ Set.range s} → Fin 2) _ ℂ)).submatrix
      (tvSplit s) (tvSplit s) := by
  classical
  ext x y
  change (if ∀ q, q ∉ Set.range s → x q = y q then A (x ∘ s) (y ∘ s) else 0) =
    A (x ∘ s) (y ∘ s) * (1 : Matrix _ _ ℂ) (fun q : {q : Q // q ∉ Set.range s} => x q)
      (fun q : {q : Q // q ∉ Set.range s} => y q)
  simp only [Matrix.one_apply]
  have h : (∀ q, q ∉ Set.range s → x q = y q) ↔
      (fun q : {q : Q // q ∉ Set.range s} => x q) = (fun q : {q : Q // q ∉ Set.range s} => y q) := by
    simp only [funext_iff, Subtype.forall]
  simp only [h]
  split_ifs <;> simp

private lemma tv_lift_mul {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (A B : QMat k) : liftOp s (A * B) = liftOp s A * liftOp s B := by
  classical
  simp only [tv_lift_eq]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]
  simp

private lemma tv_lift_star {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (A : QMat k) :
    liftOp s Aᴴ = (liftOp s A)ᴴ := by
  classical
  simp only [tv_lift_eq, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

private lemma tv_lift_one {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q) : liftOp s 1 = 1 := by
  classical
  simp only [tv_lift_eq, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

private lemma tv_lift_sum {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (L : List (QMat k)) :
    liftOp s L.sum = (L.map (liftOp s)).sum := by
  classical
  induction L with
  | nil => ext x y; simp [liftOp]
  | cons A L ih =>
    simp only [List.sum_cons, List.map_cons, ← ih]
    ext x y
    simp only [liftOp, Matrix.add_apply]
    split_ifs <;> simp

private lemma tv_complete_lift {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (K : List (QMat k)) (hK : (K.map fun A => Aᴴ * A).sum = 1) :
    (K.map fun A => (liftOp s A)ᴴ * liftOp s A).sum = 1 := by
  classical
  calc
    _ = liftOp s (K.map fun A => Aᴴ * A).sum := by
      simp only [tv_lift_sum, List.map_map, Function.comp_def, tv_lift_mul, tv_lift_star]
    _ = liftOp s 1 := by rw [hK]
    _ = 1 := tv_lift_one s

private lemma tv_apply_pos {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k)) {ρ : Op Q} (hρ : ρ.PosSemidef) :
    (applyKraus s K ρ).PosSemidef := by
  induction K with
  | nil => exact Matrix.PosSemidef.zero
  | cons A K ih =>
    exact (hρ.mul_mul_conjTranspose_same (liftOp s A)).add ih

private lemma tv_apply_linear {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k)) (ρ σ : Op Q) (a : ℝ) :
    applyKraus s K (ρ - a • σ) = applyKraus s K ρ - a • applyKraus s K σ := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ih]
    module

private lemma tv_apply_trace_aux {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k)) (ρ : Op Q) :
    (applyKraus s K ρ).trace =
      (ρ * (K.map fun A => (liftOp s A)ᴴ * liftOp s A).sum).trace := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, ih]
    congr 1
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]

private lemma tv_apply_trace {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k))
    (hK : (K.map fun A => Aᴴ * A).sum = 1) (ρ : Op Q) :
    (applyKraus s K ρ).trace = ρ.trace := by
  rw [tv_apply_trace_aux, tv_complete_lift s K hK, Matrix.mul_one]

private lemma tv_gate_complete (g : Gate) : g.unitaryᴴ * g.unitary = 1 := by
  classical
  have hu1 : (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} := by decide
  have hu2 : (Finset.univ : Finset (Fin 2 → Fin 2)) = {![0,0], ![0,1], ![1,0], ![1,1]} := by decide
  have hc1 (x : Fin 1 → Fin 2) : x = ![0] ∨ x = ![1] := by
    have h := Finset.mem_univ x
    simpa only [hu1, Finset.mem_insert, Finset.mem_singleton] using h
  have hc2 (x : Fin 2 → Fin 2) : x = ![0,0] ∨ x = ![0,1] ∨ x = ![1,0] ∨ x = ![1,1] := by
    have h := Finset.mem_univ x
    simpa only [hu2, Finset.mem_insert, Finset.mem_singleton] using h
  cases g with
  | H =>
    change hadamardMatᴴ * hadamardMat = 1
    have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      norm_cast
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [hadamardMat, hu1, Complex.conj_ofReal, ← div_pow,
        div_mul_div_comm, hs, hn] <;>
      field_simp [hn] <;> first | (simpa only [pow_two] using hs.symm) | ring
  | T =>
    change tMatᴴ * tMat = 1
    have he : starRingEnd ℂ (Complex.exp ((Real.pi : ℂ) / 4 * Complex.I)) *
        Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp [map_div, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [tMat, hu1, he]
  | CNOT =>
    change cnotMatᴴ * cnotMat = 1
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc2 x with rfl | rfl | rfl | rfl <;>
      rcases hc2 y with rfl | rfl | rfl | rfl <;>
      simp [cnotMat, hu2]

private lemma tv_ideal_complete (o : Operation) :
    (o.idealKraus.map fun A => Aᴴ * A).sum = 1 := by
  classical
  have hu1 : (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} := by decide
  have hc1 (x : Fin 1 → Fin 2) : x = ![0] ∨ x = ![1] := by
    have h := Finset.mem_univ x
    simpa only [hu1, Finset.mem_insert, Finset.mem_singleton] using h
  cases o with
  | gate g =>
    change g.unitaryᴴ * g.unitary + 0 = 1
    simpa using tv_gate_complete g
  | wait => simp [Operation.idealKraus]
  | prep =>
    change (resetKraus 0)ᴴ * resetKraus 0 + ((resetKraus 1)ᴴ * resetKraus 1 + 0) = 1
    simp only [add_zero]
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [resetKraus, hu1, Matrix.mul_apply, Matrix.conjTranspose_apply]

private def tvInv {Q : Type*} [Fintype Q] [DecidableEq Q] (σ ρ : Op Q) (w : ℝ) : Prop :=
  σ.PosSemidef ∧ ρ.PosSemidef ∧ σ.trace = 1 ∧ ρ.trace = 1 ∧
    0 ≤ w ∧ w ≤ 1 ∧ (σ - w • ρ).PosSemidef

private lemma tv_step {Q : Type*} [Fintype Q] [DecidableEq Q] (p : ℝ) (hp : p ≤ 1)
    (N : NoiseModel p) (t j : ℕ) (ℓ : Location Q) (σ ρ : Op Q) (w : ℝ)
    (h : tvInv σ ρ w) :
    ∃ v : ℝ,
      tvInv ((1 - N.prob t j) • applyKraus ℓ.support ℓ.op.idealKraus σ +
        N.prob t j • applyKraus ℓ.support (N.fault t j ℓ.op.arity).kraus σ)
        (applyKraus ℓ.support ℓ.op.idealKraus ρ) v ∧
      1 - v ≤ 1 - w + p := by
  obtain ⟨hσ, hρ, htσ, htρ, hw0, hw1, hr⟩ := h
  have hq0 := N.prob_nonneg t j
  have hqp := N.prob_le t j
  have hq1 : N.prob t j ≤ 1 := hqp.trans hp
  have hIc := tv_ideal_complete ℓ.op
  have hFc := (N.fault t j ℓ.op.arity).trace_preserving
  have hIσ := tv_apply_pos ℓ.support ℓ.op.idealKraus hσ
  have hFσ := tv_apply_pos ℓ.support (N.fault t j ℓ.op.arity).kraus hσ
  have hIρ := tv_apply_pos ℓ.support ℓ.op.idealKraus hρ
  refine ⟨(1 - N.prob t j) * w, ⟨(hIσ.smul (sub_nonneg.2 hq1)).add (hFσ.smul hq0),
    hIρ, ?_, ?_, mul_nonneg (sub_nonneg.2 hq1) hw0, ?_, ?_⟩, ?_⟩
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      tv_apply_trace _ _ hIc, tv_apply_trace _ _ hFc, htσ]
    simp
  · rw [tv_apply_trace _ _ hIc, htρ]
  · nlinarith [mul_nonneg hq0 hw0]
  · have hpR := (tv_apply_pos ℓ.support ℓ.op.idealKraus hr).smul (sub_nonneg.2 hq1)
    rw [tv_apply_linear] at hpR
    convert hpR.add (hFσ.smul hq0) using 1 <;> module
  · nlinarith [mul_nonneg hq0 (sub_nonneg.2 hw1)]

private lemma tv_fold {S α : Type*} (P : S → S → ℝ → Prop)
    (I F : α → S → S) (cost : α → ℝ)
    (hstep : ∀ a σ ρ w, P σ ρ w →
      ∃ v, P (F a σ) (I a ρ) v ∧ 1 - v ≤ 1 - w + cost a)
    (L : List α) (σ ρ : S) (w : ℝ) (h : P σ ρ w) :
    ∃ v, P (L.foldl (fun x a => F a x) σ) (L.foldl (fun x a => I a x) ρ) v ∧
      1 - v ≤ 1 - w + (L.map cost).sum := by
  induction L generalizing σ ρ w with
  | nil => exact ⟨w, h, by simp⟩
  | cons a L ih =>
    obtain ⟨u, hu, huc⟩ := hstep a σ ρ w h
    obtain ⟨v, hv, hvc⟩ := ih (F a σ) (I a ρ) u hu
    refine ⟨v, hv, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    linarith

private lemma tv_layer {Q : Type*} [Fintype Q] [DecidableEq Q] (p : ℝ) (hp : p ≤ 1)
    (N : NoiseModel p) (t : ℕ) (L : Layer Q) (σ ρ : Op Q) (w : ℝ)
    (h : tvInv σ ρ w) :
    ∃ v, tvInv (noisyLayer N t L σ) (idealLayer L ρ) v ∧
      1 - v ≤ 1 - w + p * L.locs.length := by
  have hzip : L.locs.zipIdx.foldl (fun x (a : Location Q × ℕ) =>
      applyKraus a.1.support a.1.op.idealKraus x) ρ = idealLayer L ρ := by
    rw [← List.foldl_map (f := Prod.fst)
      (g := fun x (a : Location Q) => applyKraus a.support a.op.idealKraus x)]
    simp only [List.zipIdx_map_fst, idealLayer]
  have H := tv_fold tvInv
    (fun (a : Location Q × ℕ) x => applyKraus a.1.support a.1.op.idealKraus x)
    (fun (a : Location Q × ℕ) x =>
      (1 - N.prob t a.2) • applyKraus a.1.support a.1.op.idealKraus x +
        N.prob t a.2 • applyKraus a.1.support (N.fault t a.2 a.1.op.arity).kraus x)
    (fun _ => p) (fun a σ ρ w h => tv_step p hp N t a.2 a.1 σ ρ w h)
    L.locs.zipIdx σ ρ w h
  simpa [noisyLayer, hzip, List.map_const', List.length_zipIdx,
    List.sum_replicate, nsmul_eq_mul, mul_comm] using H

private lemma tv_init {Q : Type*} [Fintype Q] [DecidableEq Q] :
    tvInv (initState Q) (initState Q) 1 := by
  classical
  have hd : initState Q = Matrix.diagonal (fun x : Q → Fin 2 => if x = 0 then (1 : ℂ) else 0) := by
    ext x y
    by_cases h : x = y
    · subst y; simp [initState, Matrix.diagonal]
    · simp [initState, Matrix.diagonal, h]
      intro hx hy
      apply h
      rw [hx, hy]
  have hpos : (initState Q).PosSemidef := by
    rw [hd]
    apply Matrix.PosSemidef.diagonal
    intro x
    change 0 ≤ if x = 0 then (1 : ℂ) else 0
    split_ifs <;> simp
  have ht : (initState Q).trace = 1 := by simp [initState, Matrix.trace]
  refine ⟨hpos, hpos, ht, ht, by norm_num, le_rfl, ?_⟩
  simpa only [one_smul, sub_self] using (Matrix.PosSemidef.zero : (0 : Op Q).PosSemidef)

private lemma tv_bound {Q : Type*} [Fintype Q] [DecidableEq Q] (σ ρ : Op Q) (w : ℝ)
    (h : tvInv σ ρ w) : tvDist (outDist σ) (outDist ρ) ≤ 1 - w := by
  classical
  obtain ⟨hσ, hρ, htσ, htρ, hw0, hw1, hr⟩ := h
  have hsσ : ∑ x, (σ x x).re = 1 := by
    rw [← Complex.re_sum]
    change σ.trace.re = 1
    rw [htσ]; rfl
  have hsρ : ∑ x, (ρ x x).re = 1 := by
    rw [← Complex.re_sum]
    change ρ.trace.re = 1
    rw [htρ]; rfl
  have hab (x : Q → Fin 2) : |(σ x x).re - (ρ x x).re| ≤
      (σ x x).re + (ρ x x).re - 2 * w * (ρ x x).re := by
    have hb := (Complex.nonneg_iff.1 (hρ.diag_nonneg (i := x))).1
    have hrx := (Complex.nonneg_iff.1 (hr.diag_nonneg (i := x))).1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.sub_re, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hrx
    exact abs_le.2 ⟨by nlinarith, by nlinarith [mul_nonneg (sub_nonneg.2 hw1) hb]⟩
  calc
    tvDist (outDist σ) (outDist ρ) =
        (1 / 2 : ℝ) * ∑ x, |(σ x x).re - (ρ x x).re| := rfl
    _ ≤ (1 / 2 : ℝ) * ∑ x, ((σ x x).re + (ρ x x).re - 2 * w * (ρ x x).re) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hab x) (by norm_num)
    _ = 1 - w := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsσ, hsρ]
      ring

theorem solution {Q : Type*} [Fintype Q] [DecidableEq Q]
    (C : Circuit Q) (p : ℝ) (hp : p ≤ 1) (N : NoiseModel p) :
    tvDist (outDist (noisyState N C)) (outDist (idealState C)) ≤ p * C.size := by
  have hzip : C.zipIdx.foldl (fun x (a : Layer Q × ℕ) => idealLayer a.1 x) (initState Q) =
      idealState C := by
    rw [← List.foldl_map (f := Prod.fst) (g := fun x (a : Layer Q) => idealLayer a x)]
    simp only [List.zipIdx_map_fst, idealState]
  have hcost : (C.zipIdx.map fun a => p * (a.1.locs.length : ℝ)).sum = p * C.size := by
    rw [List.sum_map_mul_left]
    have hm : (C.zipIdx.map fun a => (a.1.locs.length : ℝ)) =
        C.map (fun a => (a.locs.length : ℝ)) := by
      change C.zipIdx.map ((fun a : Layer Q => (a.locs.length : ℝ)) ∘ Prod.fst) = _
      rw [← List.map_map, List.zipIdx_map_fst]
    rw [hm]
    congr 1
    simp only [Circuit.size, Nat.cast_list_sum, List.map_map, Function.comp_def]
  obtain ⟨v, hv, hc⟩ := tv_fold tvInv
    (fun (a : Layer Q × ℕ) x => idealLayer a.1 x)
    (fun (a : Layer Q × ℕ) x => noisyLayer N a.2 a.1 x)
    (fun a => p * (a.1.locs.length : ℝ))
    (fun a σ ρ w h => tv_layer p hp N a.2 a.1 σ ρ w h)
    C.zipIdx (initState Q) (initState Q) 1 tv_init
  rw [hzip] at hv
  exact (tv_bound _ _ v hv).trans (by simpa only [sub_self, zero_add, hcost] using hc)

-- Prove2me | solution 1 for ThresholdTheorem.tvDist_le_malignant_pairs
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:31:21.888786+00:00
-- url     : https://prove2.me/submissions/fa571a80-bea2-45e7-b072-8a5ca2c7dacd

import Mathlib
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

/-! ## New part: multilinear expansion over a single location and union bound -/

private lemma mp_state_psd {Q : Type*} [Fintype Q] [DecidableEq Q]
    (C : Circuit Q) (N : NoiseModel 1) :
    (noisyState N C).PosSemidef ∧ (noisyState N C).trace = 1 := by
  obtain ⟨v, hv, -⟩ := tv_fold tvInv
    (fun (a : Layer Q × ℕ) x => idealLayer a.1 x)
    (fun (a : Layer Q × ℕ) x => noisyLayer N a.2 a.1 x)
    (fun a => 1 * (a.1.locs.length : ℝ))
    (fun a σ ρ w h => tv_layer 1 le_rfl N a.2 a.1 σ ρ w h)
    C.zipIdx (initState Q) (initState Q) 1 tv_init
  exact ⟨hv.1, hv.2.2.1⟩

private lemma mp_outDist_nonneg {Q : Type*} [Fintype Q] [DecidableEq Q] (σ : Op Q)
    (hσ : σ.PosSemidef) (x : Q → Fin 2) : 0 ≤ outDist σ x :=
  (Complex.nonneg_iff.1 (hσ.diag_nonneg (i := x))).1

private lemma mp_outDist_sum {Q : Type*} [Fintype Q] [DecidableEq Q] (σ : Op Q)
    (ht : σ.trace = 1) : ∑ x, outDist σ x = 1 := by
  unfold outDist
  rw [← Complex.re_sum]
  change σ.trace.re = 1
  rw [ht]; rfl

private lemma mp_decode_nonneg {n b : ℕ} (dec : (Fin b → Fin 2) → Fin 2)
    (P : (Fin n × Fin b → Fin 2) → ℝ) (hP : ∀ x, 0 ≤ P x) (y : Fin n → Fin 2) :
    0 ≤ decodeDist dec P y :=
  Finset.sum_nonneg fun x _ => hP x

private lemma mp_decode_sum {n b : ℕ} (dec : (Fin b → Fin 2) → Fin 2)
    (P : (Fin n × Fin b → Fin 2) → ℝ) : ∑ y, decodeDist dec P y = ∑ x, P x := by
  classical
  unfold decodeDist
  exact Finset.sum_fiberwise Finset.univ (fun x : Fin n × Fin b → Fin 2 =>
    (fun i => dec (fun j => x (i, j)))) P

private lemma mp_tv_le_one {α : Type*} [Fintype α] (f g : α → ℝ)
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (hsf : ∑ y, f y = 1) (hsg : ∑ y, g y = 1) :
    tvDist f g ≤ 1 := by
  unfold tvDist
  have : ∑ y, |f y - g y| ≤ ∑ y, (f y + g y) :=
    Finset.sum_le_sum fun y _ => abs_le.2 ⟨by linarith [hf y, hg y], by linarith [hf y, hg y]⟩
  rw [Finset.sum_add_distrib, hsf, hsg] at this
  linarith

/-- One noisy location, with fault probabilities `q` and fault channels `F`. -/
private noncomputable def mpStep {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ) (σ : Op Q)
    (e : Location Q × (ℕ × ℕ)) : Op Q :=
  (1 - q e.2.1 e.2.2) • applyKraus e.1.support e.1.op.idealKraus σ +
    q e.2.1 e.2.2 • applyKraus e.1.support (F e.2.1 e.2.2 e.1.op.arity).kraus σ

/-- The flat list of all locations of a circuit with their coordinates `(t, j)`. -/
private def mpLocs {Q : Type*} [DecidableEq Q] (C : Circuit Q) :
    List (Location Q × (ℕ × ℕ)) :=
  C.zipIdx.flatMap (fun Lt => Lt.1.locs.zipIdx.map (fun ℓj => (ℓj.1, (Lt.2, ℓj.2))))

private lemma mp_noisyState_eq {Q : Type*} [Fintype Q] [DecidableEq Q] {p : ℝ}
    (N : NoiseModel p) (C : Circuit Q) :
    noisyState N C = (mpLocs C).foldl (mpStep N.fault N.prob) (initState Q) := by
  unfold noisyState mpLocs
  rw [List.foldl_flatMap]
  congr 1
  funext σ Lt
  rw [List.foldl_map]
  rfl

private lemma mp_locs_nodup {Q : Type*} [DecidableEq Q] (C : Circuit Q) :
    ((mpLocs C).map Prod.snd).Nodup := by
  unfold mpLocs
  rw [List.map_flatMap]
  rw [List.nodup_flatMap]
  constructor
  · intro Lt _
    rw [List.map_map]
    have : (Lt.1.locs.zipIdx.map (Prod.snd ∘ fun ℓj : Location Q × ℕ => (ℓj.1, (Lt.2, ℓj.2)))) =
        (Lt.1.locs.zipIdx.map Prod.snd).map (fun j => (Lt.2, j)) := by
      rw [List.map_map]; rfl
    rw [this, List.zipIdx_map_snd]
    exact (List.nodup_range' ).map (fun a b h => (Prod.mk.inj h).2)
  · have h1 : (C.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]; exact List.nodup_range'
    rw [List.Nodup, List.pairwise_map] at h1
    refine h1.imp fun {a b} hab => ?_
    rw [Function.onFun, List.disjoint_left]
    intro x hxa hxb
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hxa hxb
    obtain ⟨u, -, rfl⟩ := hxa
    obtain ⟨v, -, hv⟩ := hxb
    exact hab (Prod.mk.inj hv).1.symm

private lemma mp_applyKraus_comb {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k)) (a b : ℝ) (X Y : Op Q) :
    applyKraus s K (a • X + b • Y) = a • applyKraus s K X + b • applyKraus s K Y := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    module

private lemma mp_fold_comb {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ)
    (E : List (Location Q × (ℕ × ℕ))) (a b : ℝ) (X Y : Op Q) :
    E.foldl (mpStep F q) (a • X + b • Y) =
      a • E.foldl (mpStep F q) X + b • E.foldl (mpStep F q) Y := by
  induction E generalizing X Y with
  | nil => rfl
  | cons e E ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    simp only [mpStep, mp_applyKraus_comb]
    module

/-- Update of the fault probability at one location. -/
private def mpUpd (q : ℕ → ℕ → ℝ) (a : ℕ × ℕ) (v : ℝ) : ℕ → ℕ → ℝ :=
  fun t j => if (t, j) = a then v else q t j

private lemma mp_fold_congr {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : ℕ → ℕ → (k : ℕ) → Channel k) (q q' : ℕ → ℕ → ℝ)
    (E : List (Location Q × (ℕ × ℕ)))
    (h : ∀ e ∈ E, q e.2.1 e.2.2 = q' e.2.1 e.2.2) (σ : Op Q) :
    E.foldl (mpStep F q) σ = E.foldl (mpStep F q') σ :=
  List.foldl_ext _ _ _ fun σ e he => by simp only [mpStep, h e he]

private lemma mp_fold_split {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ) (a : ℕ × ℕ)
    (E : List (Location Q × (ℕ × ℕ))) (hE : (E.map Prod.snd).Nodup) (σ : Op Q) :
    E.foldl (mpStep F q) σ =
      (1 - q a.1 a.2) • E.foldl (mpStep F (mpUpd q a 0)) σ +
        q a.1 a.2 • E.foldl (mpStep F (mpUpd q a 1)) σ := by
  induction E generalizing σ with
  | nil => simp only [List.foldl_nil]; module
  | cons e E ih =>
    simp only [List.map_cons, List.nodup_cons] at hE
    obtain ⟨hnot, hE⟩ := hE
    simp only [List.foldl_cons]
    by_cases he : e.2 = a
    · have hc : ∀ v, ∀ e' ∈ E, mpUpd q a v e'.2.1 e'.2.2 = q e'.2.1 e'.2.2 := by
        intro v e' he'
        have : e'.2 ≠ a := by
          rintro h; apply hnot; rw [he, ← h]; exact List.mem_map_of_mem he'
        simp only [mpUpd, Prod.mk.eta, if_neg this]
      rw [mp_fold_congr F (mpUpd q a 0) q E (hc 0), mp_fold_congr F (mpUpd q a 1) q E (hc 1),
        ← mp_fold_comb]
      congr 1
      have h0 : mpUpd q a 0 e.2.1 e.2.2 = 0 := by simp [mpUpd, Prod.mk.eta, he]
      have h1 : mpUpd q a 1 e.2.1 e.2.2 = 1 := by simp [mpUpd, Prod.mk.eta, he]
      have hq : q e.2.1 e.2.2 = q a.1 a.2 := by rw [← he]
      simp only [mpStep, h0, h1, hq]
      module
    · have hs : ∀ v, mpStep F (mpUpd q a v) σ e = mpStep F q σ e := by
        intro v
        simp only [mpStep, mpUpd, Prod.mk.eta, if_neg he]
      rw [hs 0, hs 1]
      exact ih hE _

private noncomputable def mpBad (B : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (q : ℕ → ℕ → ℝ) : ℝ :=
  ∑ x ∈ B, q x.1.1 x.1.2 * q x.2.1 x.2.2

private lemma mp_bad_split (B : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (hB : ∀ x ∈ B, x.1 ≠ x.2)
    (q : ℕ → ℕ → ℝ) (a : ℕ × ℕ) :
    mpBad B q = (1 - q a.1 a.2) * mpBad B (mpUpd q a 0) + q a.1 a.2 * mpBad B (mpUpd q a 1) := by
  unfold mpBad
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hne := hB x hx
  simp only [mpUpd, Prod.mk.eta]
  by_cases h1 : x.1 = a
  · have h2 : x.2 ≠ a := fun h => hne (h1.trans h.symm)
    rw [if_pos h1, if_pos h1, if_neg h2, if_neg h2, ← h1]
    ring
  · by_cases h2 : x.2 = a
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2, ← h2]
      ring
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      ring

private lemma mp_bad_nonneg (B : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (q : ℕ → ℕ → ℝ)
    (hq : ∀ t j, 0 ≤ q t j) : 0 ≤ mpBad B q :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hq _ _) (hq _ _)

private lemma mp_tv_mix {α : Type*} [Fintype α] (f g h P : α → ℝ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hf : ∀ y, f y = (1 - c) * g y + c * h y) :
    tvDist f P ≤ (1 - c) * tvDist g P + c * tvDist h P := by
  unfold tvDist
  have key : ∀ y, |f y - P y| ≤ (1 - c) * |g y - P y| + c * |h y - P y| := by
    intro y
    rw [hf y]
    calc |(1 - c) * g y + c * h y - P y| = |(1 - c) * (g y - P y) + c * (h y - P y)| := by
          congr 1; ring
      _ ≤ |(1 - c) * (g y - P y)| + |c * (h y - P y)| := abs_add_le _ _
      _ = (1 - c) * |g y - P y| + c * |h y - P y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg (by linarith)]
  have hs := Finset.sum_le_sum fun y (_ : y ∈ (Finset.univ : Finset α)) => key y
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  linarith

private lemma mp_main {n b : ℕ} (dec : (Fin b → Fin 2) → Fin 2)
    (C' : Circuit (Fin n × Fin b)) (B : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hB : ∀ x ∈ B, x.1 ≠ x.2) (P : (Fin n → Fin 2) → ℝ)
    (F : ℕ → ℕ → (k : ℕ) → Channel k)
    (hgood : ∀ q : ℕ → ℕ → ℝ, (∀ t j, q t j = 0 ∨ q t j = 1) →
      (∀ x ∈ B, q x.1.1 x.1.2 = 0 ∨ q x.2.1 x.2.2 = 0) →
      decodeDist dec (outDist ((mpLocs C').foldl (mpStep F q) (initState _))) = P)
    (hdist : ∀ q : ℕ → ℕ → ℝ, (∀ t j, q t j = 0 ∨ q t j = 1) →
      (∀ y, 0 ≤ decodeDist dec (outDist ((mpLocs C').foldl (mpStep F q) (initState _))) y) ∧
      ∑ y, decodeDist dec (outDist ((mpLocs C').foldl (mpStep F q) (initState _))) y = 1)
    (T : Finset (ℕ × ℕ)) :
    ∀ q : ℕ → ℕ → ℝ, (∀ t j, 0 ≤ q t j ∧ q t j ≤ 1) →
      (∀ t j, (t, j) ∉ T → q t j = 0 ∨ q t j = 1) →
      tvDist (decodeDist dec (outDist ((mpLocs C').foldl (mpStep F q) (initState _)))) P
        ≤ mpBad B q := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro q hq h01
    have h01' : ∀ t j, q t j = 0 ∨ q t j = 1 := fun t j => h01 t j (Finset.notMem_empty _)
    by_cases hav : ∀ x ∈ B, q x.1.1 x.1.2 = 0 ∨ q x.2.1 x.2.2 = 0
    · rw [hgood q h01' hav]
      have : tvDist P P = 0 := by simp [tvDist]
      rw [this]
      exact mp_bad_nonneg B q fun t j => (hq t j).1
    · push_neg at hav
      obtain ⟨x, hx, h1, h2⟩ := hav
      have e1 : q x.1.1 x.1.2 = 1 := (h01' _ _).resolve_left h1
      have e2 : q x.2.1 x.2.2 = 1 := (h01' _ _).resolve_left h2
      have hbad : 1 ≤ mpBad B q := by
        have := Finset.single_le_sum (f := fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
          q x.1.1 x.1.2 * q x.2.1 x.2.2)
          (fun y _ => mul_nonneg (hq _ _).1 (hq _ _).1) hx
        simp only [e1, e2, mul_one] at this
        exact this
      let z : ℕ → ℕ → ℝ := fun _ _ => 0
      have h0 : ∀ t j, z t j = 0 ∨ z t j = 1 := fun _ _ => Or.inl rfl
      have hP := hgood z h0 (fun _ _ => Or.inl rfl)
      obtain ⟨hn0, hs0⟩ := hdist _ h0
      obtain ⟨hnq, hsq⟩ := hdist q h01'
      rw [hP] at hn0 hs0
      exact (mp_tv_le_one _ _ hnq hn0 hsq hs0).trans hbad
  | insert a T haT ih =>
    intro q hq h01
    have hc0 := (hq a.1 a.2).1
    have hc1 := (hq a.1 a.2).2
    have hupd : ∀ v, (v = 0 ∨ v = 1) → (∀ t j, 0 ≤ mpUpd q a v t j ∧ mpUpd q a v t j ≤ 1) ∧
        (∀ t j, (t, j) ∉ T → mpUpd q a v t j = 0 ∨ mpUpd q a v t j = 1) := by
      intro v hv
      constructor
      · intro t j
        unfold mpUpd
        split_ifs
        · rcases hv with rfl | rfl <;> norm_num
        · exact hq t j
      · intro t j htj
        unfold mpUpd
        split_ifs with h
        · exact hv
        · exact h01 t j (by
            rw [Finset.mem_insert, not_or]; exact ⟨h, htj⟩)
    obtain ⟨h0a, h0b⟩ := hupd 0 (Or.inl rfl)
    obtain ⟨h1a, h1b⟩ := hupd 1 (Or.inr rfl)
    have i0 := ih _ h0a h0b
    have i1 := ih _ h1a h1b
    have hsplit := mp_fold_split F q a (mpLocs C') (mp_locs_nodup C') (initState _)
    rw [mp_bad_split B hB q a]
    refine (mp_tv_mix _
      (decodeDist dec (outDist ((mpLocs C').foldl (mpStep F (mpUpd q a 0)) (initState _))))
      (decodeDist dec (outDist ((mpLocs C').foldl (mpStep F (mpUpd q a 1)) (initState _))))
      P (q a.1 a.2) hc0 hc1 ?_).trans ?_
    · intro y
      rw [hsplit]
      unfold decodeDist outDist
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Matrix.add_apply, Matrix.smul_apply, Complex.add_re, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    · have := sub_nonneg.2 hc1
      nlinarith [mul_le_mul_of_nonneg_left i0 this, mul_le_mul_of_nonneg_left i1 hc0]

theorem solution {n b : ℕ} (dec : (Fin b → Fin 2) → Fin 2)
    (C' : Circuit (Fin n × Fin b)) (B : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hB : ∀ x ∈ B, x.1 ≠ x.2) (P : (Fin n → Fin 2) → ℝ)
    (p : ℝ) (hp : p ≤ 1) (N : NoiseModel p)
    (hgood : ∀ N' : NoiseModel 1, (∀ t j, N'.fault t j = N.fault t j) →
      (∀ t j, N'.prob t j = 0 ∨ N'.prob t j = 1) →
      (∀ x ∈ B, N'.prob x.1.1 x.1.2 = 0 ∨ N'.prob x.2.1 x.2.2 = 0) →
      decodeDist dec (outDist (noisyState N' C')) = P) :
    tvDist (decodeDist dec (outDist (noisyState N C'))) P ≤ B.card * p ^ 2 := by
  classical
  -- deterministic fault patterns as noise models of rate 1
  let mk : ∀ q : ℕ → ℕ → ℝ, (∀ t j, q t j = 0 ∨ q t j = 1) → NoiseModel 1 :=
    fun q h01 =>
      { prob := q
        fault := N.fault
        prob_nonneg := fun t j => by
          rcases h01 t j with h | h <;> rw [h] <;> norm_num
        prob_le := fun t j => by
          rcases h01 t j with h | h <;> rw [h] <;> norm_num }
  have hgood' : ∀ q : ℕ → ℕ → ℝ, (∀ t j, q t j = 0 ∨ q t j = 1) →
      (∀ x ∈ B, q x.1.1 x.1.2 = 0 ∨ q x.2.1 x.2.2 = 0) →
      decodeDist dec (outDist ((mpLocs C').foldl (mpStep N.fault q) (initState _))) = P := by
    intro q h01 hav
    have := hgood (mk q h01) (fun _ _ => rfl) h01 hav
    rwa [mp_noisyState_eq] at this
  have hdist : ∀ q : ℕ → ℕ → ℝ, (∀ t j, q t j = 0 ∨ q t j = 1) →
      (∀ y, 0 ≤ decodeDist dec (outDist ((mpLocs C').foldl (mpStep N.fault q) (initState _))) y) ∧
      ∑ y, decodeDist dec (outDist ((mpLocs C').foldl (mpStep N.fault q) (initState _))) y = 1 := by
    intro q h01
    obtain ⟨hpsd, htr⟩ := mp_state_psd C' (mk q h01)
    rw [mp_noisyState_eq] at hpsd htr
    exact ⟨mp_decode_nonneg dec _ (mp_outDist_nonneg _ hpsd),
      by rw [mp_decode_sum]; exact mp_outDist_sum _ htr⟩
  let S : Finset (ℕ × ℕ) := ((mpLocs C').map Prod.snd).toFinset
  let q0 : ℕ → ℕ → ℝ := fun t j => if (t, j) ∈ S then N.prob t j else 0
  have hq0 : ∀ t j, 0 ≤ q0 t j ∧ q0 t j ≤ p := by
    intro t j
    simp only [q0]
    split_ifs
    · exact ⟨N.prob_nonneg t j, N.prob_le t j⟩
    · exact ⟨le_rfl, (N.prob_nonneg 0 0).trans (N.prob_le 0 0)⟩
  have heq : noisyState N C' = (mpLocs C').foldl (mpStep N.fault q0) (initState _) := by
    rw [mp_noisyState_eq]
    refine mp_fold_congr _ _ _ _ (fun e he => ?_) _
    have : (e.2.1, e.2.2) ∈ S := by
      simp only [S, Prod.mk.eta, List.mem_toFinset]
      exact List.mem_map_of_mem he
    simp only [q0, if_pos this]
  have key := mp_main dec C' B hB P N.fault hgood' hdist S q0
    (fun t j => ⟨(hq0 t j).1, (hq0 t j).2.trans hp⟩)
    (fun t j h => Or.inl (by simp only [q0, if_neg h]))
  rw [heq]
  refine key.trans ?_
  unfold mpBad
  calc ∑ x ∈ B, q0 x.1.1 x.1.2 * q0 x.2.1 x.2.2 ≤ ∑ _x ∈ B, p ^ 2 :=
        Finset.sum_le_sum fun x _ => by
          rw [sq]
          exact mul_le_mul (hq0 _ _).2 (hq0 _ _).2 (hq0 _ _).1
            ((hq0 0 0).1.trans (hq0 0 0).2)
    _ = B.card * p ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]

-- Prove2me | solution 1 for ThresholdTheorem.noiseModel_isLocalStochastic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:41:43.311888+00:00
-- url     : https://prove2.me/submissions/ea53a4fd-466d-4a9f-835f-725eb921efe6

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

open Matrix
open ThresholdTheorem

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


/-! ## Transport from `Q` to `Q ⊕ Fin 0` -/

private noncomputable def nmE (Q : Type*) : (Q ⊕ Fin 0 → Fin 2) ≃ (Q → Fin 2) :=
  Equiv.arrowCongr (Equiv.sumEmpty Q (Fin 0)) (Equiv.refl (Fin 2))

private lemma nmE_apply {Q : Type*} (x : Q ⊕ Fin 0 → Fin 2) : nmE Q x = fun q => x (Sum.inl q) := by
  funext q; simp [nmE]

private noncomputable def nmPhi {Q : Type*} (ρ : Op Q) : Op (Q ⊕ Fin 0) :=
  ρ.submatrix (nmE Q) (nmE Q)

private lemma nmPhi_lift {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (s' : Fin k ↪ Q ⊕ Fin 0) (hs : ∀ i, s' i = Sum.inl (s i)) (A : QMat k) :
    nmPhi (liftOp s A) = liftOp s' A := by
  classical
  ext x y
  simp only [nmPhi, submatrix_apply, liftOp, nmE_apply]
  have h1 : (fun i => x (s' i)) = (fun i => x (Sum.inl (s i))) := funext fun i => by rw [hs]
  have h2 : (fun i => y (s' i)) = (fun i => y (Sum.inl (s i))) := funext fun i => by rw [hs]
  have hc : (∀ q, q ∉ Set.range s → x (Sum.inl q) = y (Sum.inl q)) ↔
      (∀ z, z ∉ Set.range s' → x z = y z) := by
    constructor
    · intro h z hz
      rcases z with q | e
      · apply h q
        rintro ⟨i, rfl⟩
        exact hz ⟨i, hs i⟩
      · exact e.elim0
    · intro h q hq
      apply h
      rintro ⟨i, hi⟩
      rw [hs] at hi
      exact hq ⟨i, Sum.inl_injective hi⟩
  simp only [Function.comp_def, hc, h1, h2]

private lemma nmPhi_apply {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (s' : Fin k ↪ Q ⊕ Fin 0) (hs : ∀ i, s' i = Sum.inl (s i)) (K : List (QMat k)) (ρ : Op Q) :
    nmPhi (applyKraus s K ρ) = applyKraus s' K (nmPhi ρ) := by
  induction K with
  | nil => simp [applyKraus, nmPhi]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, ← nmPhi_lift s s' hs]
    simp only [nmPhi, submatrix_mul_equiv, conjTranspose_submatrix]
    rfl

private lemma nmPhi_init {Q : Type*} : nmPhi (initState Q) = initState (Q ⊕ Fin 0) := by
  classical
  ext x y
  simp only [nmPhi, submatrix_apply, initState, nmE_apply]
  have hz : ∀ z : Q ⊕ Fin 0 → Fin 2, ((fun q => z (Sum.inl q)) = 0) ↔ z = 0 := by
    intro z
    constructor
    · intro h; funext w
      rcases w with q | e
      · exact congrFun h q
      · exact e.elim0
    · rintro rfl; rfl
  simp only [hz]

private lemma nmPhi_data {Q : Type*} (ρ : Op Q) (x : Q → Fin 2) :
    dataOutDist (nmPhi ρ) x = outDist ρ x := by
  simp only [dataOutDist, nmPhi, submatrix_apply, nmE_apply, Fintype.sum_unique, outDist]
  rfl

private lemma nm_envEmbed {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (i : Fin (k + 0)) :
    envEmbed 0 s i = Sum.inl (s i) := by
  simp [envEmbed, Fin.addCases]
  rfl

/-! ## Faulty executions as a flat fold -/

private noncomputable def nmFStep {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + 0)) (σ : Op (Q ⊕ Fin 0))
    (e : Location Q × (ℕ × ℕ)) : Op (Q ⊕ Fin 0) :=
  if (e.2.1, e.2.2) ∈ F then
    applyKraus (envEmbed 0 e.1.support) (fault e.2.1 e.2.2 e.1.op.arity).kraus σ
  else
    applyKraus (e.1.support.trans Function.Embedding.inl) e.1.op.idealKraus σ

private lemma nm_faultyState_eq {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + 0)) (C : Circuit Q) :
    faultyState F fault C = (mpLocs C).foldl (nmFStep F fault) (initState (Q ⊕ Fin 0)) := by
  unfold faultyState mpLocs
  rw [List.foldl_flatMap]
  congr 1
  funext σ Lt
  rw [List.foldl_map]
  rfl

private lemma nm_fold_rel {Q : Type*} [Fintype Q] [DecidableEq Q]
    (fault : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ) (F : Finset (ℕ × ℕ))
    (E : List (Location Q × (ℕ × ℕ)))
    (hE : ∀ e ∈ E, (q e.2.1 e.2.2 = 1 ∧ (e.2.1, e.2.2) ∈ F) ∨
      (q e.2.1 e.2.2 = 0 ∧ (e.2.1, e.2.2) ∉ F)) (σ : Op Q) :
    nmPhi (E.foldl (mpStep fault q) σ) = E.foldl (nmFStep F fault) (nmPhi σ) := by
  induction E generalizing σ with
  | nil => rfl
  | cons e E ih =>
    simp only [List.foldl_cons]
    rw [ih (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))]
    congr 1
    rcases hE e List.mem_cons_self with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [mpStep, nmFStep, h1, if_pos h2, sub_self, zero_smul, one_smul, zero_add]
      exact nmPhi_apply _ _ (nm_envEmbed _) _ _
    · simp only [mpStep, nmFStep, h1, if_neg h2, sub_zero, zero_smul, one_smul, add_zero]
      exact nmPhi_apply _ _ (fun i => rfl) _ _

/-! ## Local stochastic mixtures with a per-location bound -/

private def nmLS {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q)
    (fault : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ) (P : (Q → Fin 2) → ℝ) : Prop :=
  ∃ (r : ℕ) (w : Fin r → ℝ) (F : Fin r → Finset (ℕ × ℕ)),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    (∀ S : Finset (ℕ × ℕ), ∑ i ∈ Finset.univ.filter (fun i => S ⊆ F i), w i ≤
      ∏ l ∈ S, q l.1 l.2) ∧
    P = fun x => ∑ i, w i * dataOutDist (faultyState (m := 0) (F i) fault C) x

private lemma nm_base {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q)
    (fault : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ)
    (h01 : ∀ t j, q t j = 0 ∨ q t j = 1) :
    nmLS C fault q (outDist ((mpLocs C).foldl (mpStep fault q) (initState Q))) := by
  classical
  let F : Finset (ℕ × ℕ) := ((mpLocs C).map Prod.snd).toFinset.filter (fun l => q l.1 l.2 = 1)
  refine ⟨1, fun _ => 1, fun _ => F, fun _ => zero_le_one, by simp, ?_, ?_⟩
  · intro S
    rw [Finset.sum_filter, Fin.sum_univ_one]
    split_ifs with hS
    · refine le_of_eq (Finset.prod_eq_one fun l hl => ?_).symm
      exact (Finset.mem_filter.1 (hS hl)).2
    · exact Finset.prod_nonneg fun l _ => by rcases h01 l.1 l.2 with h | h <;> rw [h] <;> norm_num
  · funext x
    rw [Fin.sum_univ_one, one_mul, nm_faultyState_eq, ← nmPhi_init,
      ← nm_fold_rel fault q F, nmPhi_data]
    intro e he
    have hm : (e.2.1, e.2.2) ∈ ((mpLocs C).map Prod.snd).toFinset := by
      simp only [Prod.mk.eta, List.mem_toFinset]
      exact List.mem_map_of_mem he
    rcases h01 e.2.1 e.2.2 with h | h
    · right
      refine ⟨h, fun hF => ?_⟩
      have := (Finset.mem_filter.1 hF).2
      rw [h] at this
      norm_num at this
    · left
      exact ⟨h, Finset.mem_filter.2 ⟨hm, h⟩⟩

private lemma nm_mix {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q)
    (fault : ℕ → ℕ → (k : ℕ) → Channel k) (q q0 q1 : ℕ → ℕ → ℝ) (P0 P1 : (Q → Fin 2) → ℝ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h0 : nmLS C fault q0 P0) (h1 : nmLS C fault q1 P1)
    (hb : ∀ S : Finset (ℕ × ℕ),
      (1 - c) * ∏ l ∈ S, q0 l.1 l.2 + c * ∏ l ∈ S, q1 l.1 l.2 ≤ ∏ l ∈ S, q l.1 l.2) :
    nmLS C fault q (fun x => (1 - c) * P0 x + c * P1 x) := by
  classical
  obtain ⟨r0, w0, F0, hw0, hs0, hb0, rfl⟩ := h0
  obtain ⟨r1, w1, F1, hw1, hs1, hb1, rfl⟩ := h1
  have hc' : 0 ≤ 1 - c := sub_nonneg.2 hc1
  refine ⟨r0 + r1, Fin.append (fun i => (1 - c) * w0 i) (fun i => c * w1 i),
    Fin.append F0 F1, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact mul_nonneg hc' (hw0 i)
    · simp only [Fin.append_right]; exact mul_nonneg hc0 (hw1 i)
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, ← Finset.mul_sum, hs0, hs1]
    ring
  · intro S
    rw [Finset.sum_filter, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have e0 : (∑ i : Fin r0, if S ⊆ F0 i then (1 - c) * w0 i else 0) =
        (1 - c) * ∑ i ∈ Finset.univ.filter (fun i => S ⊆ F0 i), w0 i := by
      rw [Finset.mul_sum, Finset.sum_filter]
    have e1 : (∑ i : Fin r1, if S ⊆ F1 i then c * w1 i else 0) =
        c * ∑ i ∈ Finset.univ.filter (fun i => S ⊆ F1 i), w1 i := by
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [e0, e1]
    refine le_trans ?_ (hb S)
    exact add_le_add (mul_le_mul_of_nonneg_left (hb0 S) hc')
      (mul_le_mul_of_nonneg_left (hb1 S) hc0)
  · funext x
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.mul_sum, mul_assoc]

private lemma nm_prod_split (q : ℕ → ℕ → ℝ) (a : ℕ × ℕ) (S : Finset (ℕ × ℕ)) :
    (1 - q a.1 a.2) * ∏ l ∈ S, mpUpd q a 0 l.1 l.2 + q a.1 a.2 * ∏ l ∈ S, mpUpd q a 1 l.1 l.2 =
      ∏ l ∈ S, q l.1 l.2 := by
  classical
  have hrest : ∀ v, ∀ T : Finset (ℕ × ℕ), a ∉ T →
      ∏ l ∈ T, mpUpd q a v l.1 l.2 = ∏ l ∈ T, q l.1 l.2 := by
    intro v T hT
    refine Finset.prod_congr rfl fun l hl => ?_
    have : l ≠ a := fun h => hT (h ▸ hl)
    simp only [mpUpd, Prod.mk.eta, if_neg this]
  by_cases ha : a ∈ S
  · rw [← Finset.mul_prod_erase S _ ha, ← Finset.mul_prod_erase S _ ha,
      ← Finset.mul_prod_erase S (fun l => q l.1 l.2) ha,
      hrest 0 _ (Finset.notMem_erase a S), hrest 1 _ (Finset.notMem_erase a S)]
    simp only [mpUpd, Prod.mk.eta, if_true]
    ring
  · rw [hrest 0 S ha, hrest 1 S ha]
    ring

private lemma nm_main {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q)
    (fault : ℕ → ℕ → (k : ℕ) → Channel k) (T : Finset (ℕ × ℕ)) :
    ∀ q : ℕ → ℕ → ℝ, (∀ t j, 0 ≤ q t j ∧ q t j ≤ 1) →
      (∀ t j, (t, j) ∉ T → q t j = 0 ∨ q t j = 1) →
      nmLS C fault q (outDist ((mpLocs C).foldl (mpStep fault q) (initState Q))) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro q _ h01
    exact nm_base C fault q fun t j => h01 t j (Finset.notMem_empty _)
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
    have hsplit := mp_fold_split fault q a (mpLocs C) (mp_locs_nodup C) (initState Q)
    have hP : outDist ((mpLocs C).foldl (mpStep fault q) (initState Q)) =
        fun x => (1 - q a.1 a.2) *
            outDist ((mpLocs C).foldl (mpStep fault (mpUpd q a 0)) (initState Q)) x +
          q a.1 a.2 * outDist ((mpLocs C).foldl (mpStep fault (mpUpd q a 1)) (initState Q)) x := by
      funext x
      rw [hsplit]
      simp only [outDist, Matrix.add_apply, Matrix.smul_apply, Complex.add_re,
        Complex.real_smul, Complex.re_ofReal_mul]
    rw [hP]
    exact nm_mix C fault q _ _ _ _ _ hc0 hc1 (ih _ h0a h0b) (ih _ h1a h1b)
      (fun S => le_of_eq (nm_prod_split q a S))

theorem solution {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : NoiseModel p) :
    IsLocalStochasticDist C p (outDist (noisyState N C)) := by
  classical
  let S0 : Finset (ℕ × ℕ) := ((mpLocs C).map Prod.snd).toFinset
  let q0 : ℕ → ℕ → ℝ := fun t j => if (t, j) ∈ S0 then N.prob t j else 0
  have hq0 : ∀ t j, 0 ≤ q0 t j ∧ q0 t j ≤ p := by
    intro t j
    simp only [q0]
    split_ifs
    · exact ⟨N.prob_nonneg t j, N.prob_le t j⟩
    · exact ⟨le_rfl, hp0⟩
  have heq : noisyState N C = (mpLocs C).foldl (mpStep N.fault q0) (initState _) := by
    rw [mp_noisyState_eq]
    refine mp_fold_congr _ _ _ _ (fun e he => ?_) _
    have : (e.2.1, e.2.2) ∈ S0 := by
      simp only [S0, Prod.mk.eta, List.mem_toFinset]
      exact List.mem_map_of_mem he
    simp only [q0, if_pos this]
  obtain ⟨r, w, F, hw, hs, hb, hP⟩ := nm_main C N.fault S0 q0
    (fun t j => ⟨(hq0 t j).1, (hq0 t j).2.trans hp1⟩)
    (fun t j h => Or.inl (by simp only [q0, if_neg h]))
  refine ⟨r, 0, w, F, fun _ => N.fault, hw, hs, fun S => (hb S).trans ?_, by rw [heq, hP]⟩
  calc ∏ l ∈ S, q0 l.1 l.2 ≤ ∏ _l ∈ S, p :=
        Finset.prod_le_prod (fun l _ => (hq0 _ _).1) (fun l _ => (hq0 _ _).2)
    _ = p ^ S.card := Finset.prod_const p


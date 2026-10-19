-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.good_exRec_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T10:57:50.892337+00:00
-- url     : https://prove2.me/submissions/b3a78a9d-8730-4396-9f1e-b8712f367564

import Definitions.Def_QAlgorithms_Defs_FTCircuit

open QAlgorithms
open scoped Matrix

set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

private lemma conj_linear {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) :
    IsLinearMap ℂ (conjSuperop A) := by
  constructor
  · intro X Y
    simp [conjSuperop, Matrix.mul_add, Matrix.add_mul]
  · intro c X
    simp [conjSuperop, Matrix.mul_smul, Matrix.smul_mul]

private lemma kraus_linear {ι κ K : Type*} [Fintype ι] [Fintype K]
    (A : K → Matrix κ ι ℂ) : IsLinearMap ℂ (krausApply A) := by
  constructor
  · intro X Y
    simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · intro c X
    simp [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

private lemma channel_linear {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {Φ : Superop ι κ} (h : IsChannel Φ) : IsLinearMap ℂ Φ := by
  obtain ⟨m, E, _, hE⟩ := h
  have he : Φ = krausApply E := funext hE
  rw [he]
  exact kraus_linear E

private lemma loc_linear {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (l : Loc N) (O : List Bool → ℕ × ℕ → Option Bool)
    (e : Option (Superop (Qubits N × E) (Qubits N × E)))
    (he : ∀ Φ, e = some Φ → IsLinearMap ℂ Φ) : IsLinearMap ℂ (l.apply O e) := by
  cases e with
  | none =>
    constructor
    · intro X Y
      funext r
      cases hk : l.kind <;> simp only [Loc.apply, hk, Pi.add_apply]
      · exact (kraus_linear _).map_add _ _
      · split_ifs <;> first | exact (conj_linear _).map_add _ _ | rfl
      · split_ifs <;> first | exact (conj_linear _).map_add _ _ | rfl
      · split_ifs <;> first | exact (conj_linear _).map_add _ _ | rfl
      · cases r.getLast? <;> first | exact (conj_linear _).map_add _ _ | simp
    · intro c X
      funext r
      cases hk : l.kind <;> simp only [Loc.apply, hk, Pi.smul_apply]
      · exact (kraus_linear _).map_smul _ _
      · split_ifs <;> first | exact (conj_linear _).map_smul _ _ | rfl
      · split_ifs <;> first | exact (conj_linear _).map_smul _ _ | rfl
      · split_ifs <;> first | exact (conj_linear _).map_smul _ _ | rfl
      · cases r.getLast? <;> first | exact (conj_linear _).map_smul _ _ | simp
  | some Φ =>
    have hΦ := he Φ rfl
    constructor
    · intro X Y
      funext r
      cases hk : l.kind <;> simp only [Loc.apply, hk, Pi.add_apply]
      · rw [(kraus_linear _).map_add, hΦ.map_add]
      · split_ifs <;> simp only [(conj_linear _).map_add, hΦ.map_add]
      · split_ifs <;> simp only [(conj_linear _).map_add, hΦ.map_add]
      · split_ifs <;> simp only [(conj_linear _).map_add, hΦ.map_add]
      · cases r.getLast? <;> simp only [hΦ.map_add, (conj_linear _).map_add, zero_add]
      · exact hΦ.map_add _ _
    · intro c X
      funext r
      cases hk : l.kind <;> simp only [Loc.apply, hk, Pi.smul_apply]
      · rw [(kraus_linear _).map_smul, hΦ.map_smul]
      · split_ifs <;> simp only [(conj_linear _).map_smul, hΦ.map_smul]
      · split_ifs <;> simp only [(conj_linear _).map_smul, hΦ.map_smul]
      · split_ifs <;> simp only [(conj_linear _).map_smul, hΦ.map_smul]
      · cases r.getLast? <;> simp only [hΦ.map_smul, (conj_linear _).map_smul, smul_zero]
      · exact hΦ.map_smul _ _

private lemma linear_comp {M N K : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid K] [Module ℂ M] [Module ℂ N] [Module ℂ K]
    {f : N → K} {g : M → N} (hf : IsLinearMap ℂ f) (hg : IsLinearMap ℂ g) :
    IsLinearMap ℂ (f ∘ g) := by
  exact ⟨fun x y => by simp [Function.comp_def, hg.map_add, hf.map_add],
    fun c x => by simp [Function.comp_def, hg.map_smul, hf.map_smul]⟩

private lemma runStep_linear {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (O : List Bool → ℕ × ℕ → Option Bool) (err : ErrAssign N E)
    (he : ∀ id Φ, err id = some Φ → IsLinearMap ℂ Φ)
    (s : ℕ) (ls : List (Loc N)) (j : ℕ) : IsLinearMap ℂ (runStep O err s ls j) := by
  induction ls generalizing j with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons l ls ih =>
    exact linear_comp (ih (j + 1)) (loc_linear l O (err (s,j)) (he (s,j)))

private lemma run_linear {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (C : LocCircuit N) (err : ErrAssign N E)
    (he : ∀ id Φ, err id = some Φ → IsLinearMap ℂ Φ) : IsLinearMap ℂ (C.run err) := by
  suffices ∀ ls s, IsLinearMap ℂ (C.runFrom err ls s) from this C.steps 0
  intro ls
  induction ls with
  | nil => intro s; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons st ls ih =>
    intro s
    exact linear_comp (ih (s+1)) (runStep_linear _ err he s st 0)

private lemma pauli_linear {N : ℕ} (C : LocCircuit N) (fa : PauliArrangement)
    (id : ℕ × ℕ) (Φ : Superop (Qubits N × Fin 1) (Qubits N × Fin 1))
    (h : pauliErr C fa id = some Φ) : IsLinearMap ℂ Φ := by
  unfold pauliErr at h
  split at h <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst Φ
  exact conj_linear _

private lemma gadgetOut_linear {N : ℕ} (G : LocCircuit N) (fa : PauliArrangement)
    (B : List Bool → Bool) : IsLinearMap ℂ (fun X => gadgetOut G fa X B) := by
  have hr := run_linear G (pauliErr G fa) (pauli_linear G fa)
  constructor
  · intro X Y
    have hin : (fun r : List Bool => if r = [] then X + Y else 0) =
        (fun r => if r = [] then X else 0) + (fun r => if r = [] then Y else 0) := by
      funext r; by_cases h : r = [] <;> simp [h]
    simp only [gadgetOut, hin, hr.map_add]
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> simp
  · intro c X
    have hin : (fun r : List Bool => if r = [] then c • X else 0) =
        c • (fun r => if r = [] then X else 0) := by
      funext r; by_cases h : r = [] <;> simp [h]
    simp only [gadgetOut, hin, hr.map_smul]
    simp [Pi.smul_apply, Finset.smul_sum]

private lemma ec_linear (P : FTProtocol) (fa : PauliArrangement) :
    IsLinearMap ℂ (P.ecOp fa) := by
  have hg := gadgetOut_linear P.ec fa (fun _ => true)
  have he : IsLinearMap ℂ (fun X : Matrix (Qubits P.n) (Qubits P.n) ℂ =>
      embedVia (singleLayout P.n P.A) (X.submatrix (fun x => x 0) (fun x => x 0))) := by
    constructor
    · intro X Y; ext p q; simp [embedVia, ite_add_ite]
    · intro c X; ext p q; simp [embedVia, ite_add_ite]
  have ht : IsLinearMap ℂ (fun X => (traceVia (singleLayout P.n P.A) X).submatrix
      (fun y _ => y) (fun y _ => y)) := by
    constructor
    · intro X Y; ext p q; simp [traceVia, Finset.sum_add_distrib]
    · intro c X; ext p q; simp [traceVia, Finset.mul_sum]
  exact linear_comp (f := fun X => (traceVia (singleLayout P.n P.A) X).submatrix
      (fun y _ => y) (fun y _ => y)) ht (linear_comp (f := fun X => gadgetOut P.ec fa X (fun _ => true)) hg he)

private lemma linear_expand {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : Superop ι κ} (hΦ : IsLinearMap ℂ Φ) (X : Matrix ι ι ℂ) (a b : κ) :
    Φ X a b = ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) a b := by
  classical
  have hx : X = ∑ i, ∑ j, X i j • Matrix.single i j 1 := by
    ext i j
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and]
  let L := hΦ.mk' Φ
  change L X a b = _
  conv_lhs => rw [hx, map_sum]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    IsLinearMap.mk'_apply, L]

private lemma sum_swap4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

private lemma pi_comp {ι κ τ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {k : ℕ} (Φ : Fin k → Superop κ τ) (Ψ : Fin k → Superop ι κ)
    (hΦ : ∀ i, IsLinearMap ℂ (Φ i)) :
    piSuperop Φ ∘ piSuperop Ψ = piSuperop (fun i => Φ i ∘ Ψ i) := by
  classical
  funext X
  ext y y'
  simp only [Function.comp_apply, piSuperop, Matrix.of_apply]
  simp_rw [Finset.sum_mul]
  rw [sum_swap4]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  have he (i : Fin k) :
      Φ i (Ψ i (Matrix.single (x i) (x' i) 1)) (y i) (y' i) =
        ∑ a, ∑ b, Ψ i (Matrix.single (x i) (x' i) 1) a b *
          Φ i (Matrix.single a b 1) (y i) (y' i) := linear_expand (hΦ i) _ _ _
  simp only [he]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro z' _
  ring

private lemma gate_correct (P : FTProtocol) (hP : P.IsFaultTolerant) (κ : LocKind)
    (hκ : κ.IsGateOrWait) (lead trail : Fin κ.arity → PauliArrangement)
    (gad : PauliArrangement)
    (hbudget : (∑ i, faultCount P.ec (lead i)) + faultCount (P.gadget κ) gad +
      (∑ i, faultCount P.ec (trail i)) ≤ P.t) :
    P.GateExRecCorrect κ lead trail gad ∅ := by
  classical
  rcases hP with ⟨_, _, hd, _, _, _, _, _, _, _, hga, hgb, heca, hecb⟩
  have hdl := channel_linear hd.1
  let r : Fin κ.arity → ℕ := fun i => faultCount P.ec (lead i)
  let R := faultCount (P.gadget κ) gad + ∑ i, r i
  have hR : R ≤ P.t := by dsimp [R, r]; omega
  have hli (i : Fin κ.arity) : r i ≤ P.t := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (r j))
      (Finset.mem_univ i)
    dsimp [r] at hi ⊢
    omega
  have hti (i : Fin κ.arity) : R + faultCount P.ec (trail i) ≤ P.t := by
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (faultCount P.ec (trail j)))
      (Finset.mem_univ i)
    dsimp [R, r]
    omega
  have hlead : piSuperop (fun i => P.filterOp (r i)) ∘ P.leadOp lead = P.leadOp lead := by
    unfold FTProtocol.leadOp
    rw [pi_comp (fun i => P.filterOp (r i)) (fun i => P.ecOp (lead i))
      (fun i => (show IsLinearMap ℂ (P.filterOp (r i)) from conj_linear _))]
    congr 1
    funext i
    exact heca (lead i) (hli i)
  have hleadX (X : Matrix (Fin κ.arity → Qubits P.n) (Fin κ.arity → Qubits P.n) ℂ) :
      piSuperop (fun i => P.filterOp (r i)) (P.leadOp lead X) = P.leadOp lead X :=
    congrFun hlead X
  have hout (X : Matrix (Fin κ.arity → Qubits P.n) (Fin κ.arity → Qubits P.n) ℂ) :
      piSuperop (fun _ => P.filterOp R) (P.gateOp κ gad (P.leadOp lead X)) =
        P.gateOp κ gad (P.leadOp lead X) := by
    have h := congrFun (hga κ hκ gad r hR) (P.leadOp lead X)
    dsimp only [Function.comp_apply] at h
    rw [hleadX X] at h
    exact h
  have htrail : piSuperop (fun _ : Fin κ.arity => P.dec) ∘ P.trailOp trail ∅ ∘
      piSuperop (fun _ : Fin κ.arity => P.filterOp R) =
      piSuperop (fun _ : Fin κ.arity => P.dec) ∘
        piSuperop (fun _ : Fin κ.arity => P.filterOp R) := by
    simp only [FTProtocol.trailOp, Finset.notMem_empty, if_false]
    rw [← Function.comp_assoc,
      pi_comp (fun _ => P.dec) (fun i => P.ecOp (trail i)) (fun _ => hdl),
      pi_comp (fun i => P.dec ∘ P.ecOp (trail i)) (fun _ => P.filterOp R)
        (fun i => linear_comp (f := P.dec) (g := P.ecOp (trail i)) hdl (ec_linear P (trail i))),
      pi_comp (fun _ => P.dec) (fun _ => P.filterOp R) (fun _ => hdl)]
    congr 1
    funext i
    exact hecb (trail i) R (hti i)
  unfold FTProtocol.GateExRecCorrect
  funext X
  change piSuperop (fun _ => P.dec) (P.trailOp trail ∅
      (P.gateOp κ gad (P.leadOp lead X))) =
    conjSuperop κ.idealMatrix (piSuperop (fun _ => P.dec) (P.leadOp lead X))
  calc
    _ = piSuperop (fun _ => P.dec) (P.trailOp trail ∅
        (piSuperop (fun _ => P.filterOp R) (P.gateOp κ gad (P.leadOp lead X)))) := by
      rw [hout]
    _ = piSuperop (fun _ => P.dec)
        (piSuperop (fun _ => P.filterOp R) (P.gateOp κ gad (P.leadOp lead X))) :=
      congrFun htrail _
    _ = piSuperop (fun _ => P.dec) (P.gateOp κ gad (P.leadOp lead X)) := by rw [hout]
    _ = _ := by
      have h := congrFun (hgb κ hκ gad r hR) (P.leadOp lead X)
      dsimp only [Function.comp_apply] at h
      rw [hleadX X] at h
      exact h

private lemma count_empty (P : FTProtocol) {κ : LocKind} (F : ExRecFaults κ) :
    F.count P ∅ = (∑ i, faultCount P.ec (F.lead i)) + faultCount (P.gadget κ) F.gad +
      ∑ i, faultCount P.ec (F.trail i) := by
  unfold ExRecFaults.count
  rw [Finset.filter_true_of_mem (fun i _ => Finset.notMem_empty i)]

theorem solution (P : FTProtocol) (hP : P.IsFaultTolerant) (κ : LocKind)
    (F : ExRecFaults κ) (hgood : F.count P ∅ ≤ P.t) :
    ExRecCorrect P κ F ∅ := by
  classical
  rw [count_empty] at hgood
  cases κ with
  | prep =>
    rcases hP with ⟨_, _, _, _, _, _, _, _, hpa, hpb, _, _, _, hecb⟩
    have hc : faultCount (P.gadget .prep) F.gad + faultCount P.ec (F.trail ⟨0, by decide⟩) ≤ P.t := by
      have hi := Finset.single_le_sum
        (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (faultCount P.ec (F.trail i)))
        (Finset.mem_univ (⟨0, by decide⟩ : Fin LocKind.prep.trailCount))
      omega
    have hp := hpa F.gad (by omega)
    have hb := congrFun (hecb (F.trail ⟨0, by decide⟩) (faultCount (P.gadget .prep) F.gad) hc) (P.prepState F.gad)
    simp only [Function.comp_apply, hp] at hb
    simpa only [ExRecCorrect, Finset.notMem_empty, if_false, hb] using hpb F.gad (by omega)
  | meas =>
    rcases hP with ⟨_, _, _, _, _, _, _, hm, _, _, _, _, heca, _⟩
    have hc : faultCount P.ec (F.lead ⟨0, by decide⟩) + faultCount (P.gadget .meas) F.gad ≤ P.t := by
      have hi := Finset.single_le_sum
        (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (faultCount P.ec (F.lead i)))
        (Finset.mem_univ (⟨0, by decide⟩ : Fin LocKind.meas.leadCount))
      omega
    have hl := heca (F.lead ⟨0, by decide⟩) (by omega)
    intro β
    funext X
    have h := hm F.gad (faultCount P.ec (F.lead ⟨0, by decide⟩)) hc β (P.ecOp (F.lead ⟨0, by decide⟩) X)
    have hlX := congrFun hl X
    dsimp only [Function.comp_apply] at hlX
    simpa only [Function.comp_apply, hlX] using h
  | had =>
    apply gate_correct P hP .had (Or.inl rfl)
    exact hgood
  | tgate =>
    apply gate_correct P hP .tgate (Or.inr (Or.inl rfl))
    exact hgood
  | cnot =>
    apply gate_correct P hP .cnot (Or.inr (Or.inr (Or.inl rfl)))
    exact hgood
  | wait =>
    apply gate_correct P hP .wait (Or.inr (Or.inr (Or.inr rfl)))
    exact hgood

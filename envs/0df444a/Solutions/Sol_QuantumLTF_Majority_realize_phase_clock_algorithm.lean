-- Prove2me | solution 1 for QuantumLTF.Majority.realize_phase_clock_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T12:12:27.977283+00:00
-- url     : https://prove2.me/submissions/1ee25f35-4f93-4b11-aabd-55b1ee114903

import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_QuantumLTF_Membership_gates12
import Theorems.Thm_SuperconductingQC_closure_singleQubit_CNOT_eq_top
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Majority_CompilerModel
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Definitions.Def_QuantumLTF_Sections45_Model

set_option autoImplicit false

noncomputable def compiler_range_isometry {𝕜 D E F : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : D →ₗ[𝕜] E) (g : D →ₗ[𝕜] F)
    (hn : ∀ a, ‖f a‖ = ‖g a‖) : LinearMap.range f →ₗᵢ[𝕜] LinearMap.range g := by
  classical
  have hrel (a b : D) (hab : f a = f b) : g a = g b := by
    have hh := hn (a - b)
    rw [map_sub, map_sub, hab, sub_self, norm_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp hh.symm)
  let pre (x : LinearMap.range f) : D := x.2.choose
  have hpre (x : LinearMap.range f) : f (pre x) = x.1 := x.2.choose_spec
  let toFun : LinearMap.range f → LinearMap.range g :=
    fun x => ⟨g (pre x), ⟨pre x, rfl⟩⟩
  refine { toFun := toFun, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }
  · intro x y
    apply Subtype.ext
    change g (pre (x + y)) = g (pre x) + g (pre y)
    rw [← map_add]
    apply hrel
    simp only [map_add, hpre, Submodule.coe_add]
  · intro c x
    apply Subtype.ext
    change g (pre (c • x)) = c • g (pre x)
    rw [← map_smul]
    apply hrel
    simp only [map_smul, hpre, Submodule.coe_smul]
  · intro x
    change ‖g (pre x)‖ = ‖x.1‖
    rw [← hn, hpre]

theorem compiler_range_isometry_apply {𝕜 D E F : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : D →ₗ[𝕜] E) (g : D →ₗ[𝕜] F)
    (hn : ∀ a, ‖f a‖ = ‖g a‖) (a : D) :
    (compiler_range_isometry f g hn ⟨f a, ⟨a, rfl⟩⟩ : F) = g a := by
  classical
  let x : LinearMap.range f := ⟨f a, ⟨a, rfl⟩⟩
  change g x.2.choose = g a
  have hx : f x.2.choose = f a := x.2.choose_spec
  have hh := hn (x.2.choose - a)
  rw [map_sub, map_sub, hx, sub_self, norm_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp hh.symm)

theorem compiler_range_isometry_surjective {𝕜 D E F : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : D →ₗ[𝕜] E) (g : D →ₗ[𝕜] F)
    (hn : ∀ a, ‖f a‖ = ‖g a‖) :
    Function.Surjective (compiler_range_isometry f g hn) := by
  intro y
  obtain ⟨a, ha⟩ := y.2
  refine ⟨⟨f a, ⟨a, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  rw [compiler_range_isometry_apply, ha]

/- An input-independent isometry on the entire workspace realizing the
prescribed state conversion whenever its two Gram forms agree. -/
theorem compiler_exists_workspace_isometry {𝕜 D E : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (f g : D →ₗ[𝕜] E) (hn : ∀ a, ‖f a‖ = ‖g a‖) :
    ∃ U : E →ₗᵢ[𝕜] E, ∀ a, U (f a) = g a := by
  let L : LinearMap.range f →ₗᵢ[𝕜] E :=
    (LinearMap.range g).subtypeₗᵢ.comp (compiler_range_isometry f g hn)
  refine ⟨L.extend, ?_⟩
  intro a
  have hh := LinearIsometry.extend_apply L (⟨f a, ⟨a, rfl⟩⟩ : LinearMap.range f)
  exact hh.trans (compiler_range_isometry_apply f g hn a)

/- The finite-dimensional workspace map is onto, hence is a unitary
equivalence (over either the real or complex field). -/
theorem compiler_exists_workspace_unitary {𝕜 D E : Type*} [RCLike 𝕜]
    [AddCommGroup D] [Module 𝕜 D]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (f g : D →ₗ[𝕜] E) (hn : ∀ a, ‖f a‖ = ‖g a‖) :
    ∃ U : E ≃ₗᵢ[𝕜] E, ∀ a, U (f a) = g a := by
  obtain ⟨U, hU⟩ := compiler_exists_workspace_isometry f g hn
  have hsurj : Function.Surjective U :=
    LinearMap.surjective_of_injective (f := U.toLinearMap) U.injective
  exact ⟨LinearIsometryEquiv.ofSurjective U hsurj, hU⟩

/- Matching Gram matrices give a single unitary taking every prescribed
input vector to its prescribed output vector, including dependent families. -/
theorem compiler_transport_unitary {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (J : E →ₗᵢ[𝕜] F) (U : E ≃ₗᵢ[𝕜] E) :
    ∃ V : F ≃ₗᵢ[𝕜] F, ∀ x, V (J x) = J (U x) := by
  apply compiler_exists_workspace_unitary J.toLinearMap
    (J.toLinearMap.comp U.toLinearMap)
  intro x
  simp


set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

theorem compiler_embedOp_star {k n : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (star M) w = star (embedOp M w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.star_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range w → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w → z a = y a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · simp only [if_pos h, if_pos (hiff.mp h)]
  · simp only [if_neg h, if_neg (mt hiff.mpr h), star_zero]

noncomputable def compiler_adjoint_gate {n : ℕ} (g : GateApp gates12 n) : GateApp gates12 n where
  gate := ⟨g.gate.arity, star g.gate.mat⟩
  mem := by
    rcases g.mem with ⟨hU, hlo, hhi⟩
    exact ⟨Unitary.star_mem hU, hlo, hhi⟩
  wires := g.wires

noncomputable def compiler_adjoint_circuit {n : ℕ} (c : Circuit gates12 n) : Circuit gates12 n :=
  c.reverse.map compiler_adjoint_gate

theorem compiler_circuit_append {n : ℕ} (c d : Circuit gates12 n) :
    (c ++ d).unitary = d.unitary * c.unitary := by
  simp [Circuit.unitary, List.reverse_append, List.prod_append]

theorem compiler_circuit_adjoint {n : ℕ} (c : Circuit gates12 n) :
    (compiler_adjoint_circuit c).unitary = star c.unitary := by
  induction c with
  | nil => simp [compiler_adjoint_circuit, Circuit.unitary]
  | cons g c ih =>
    simp only [compiler_adjoint_circuit, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, compiler_circuit_append] at *
    simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one] at *
    rw [star_mul]
    rw [← ih]
    simp only [compiler_adjoint_gate, compiler_embedOp_star]

theorem compiler_unitary_submatrix_equiv {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : β ≃ α) (M : Matrix α α ℂ) (hM : M ∈ Matrix.unitaryGroup α ℂ) :
    M.submatrix e e ∈ Matrix.unitaryGroup β ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change M.submatrix e e * (star M).submatrix e e = 1
  rw [Matrix.submatrix_mul_equiv M (star M) e e e,
    Matrix.mem_unitaryGroup_iff.mp hM]
  ext a b
  simp [Matrix.one_apply, e.injective.eq_iff]

def compiler_binary_index (n : ℕ) : Qubits n ≃ (Fin n → Fin 2) :=
  Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm

@[simp] theorem compiler_binary_index_apply {n : ℕ} (x : Qubits n) (i : Fin n) :
    compiler_binary_index n x i = finTwoEquiv.symm (x i) := rfl

def compiler_single_index : Qubits 1 ≃ Fin 2 where
  toFun x := finTwoEquiv.symm (x 0)
  invFun a := fun _ => finTwoEquiv a
  left_inv x := by ext i; fin_cases i; simp
  right_inv a := by simp

noncomputable def compiler_one_qubit_placement {n : ℕ} (i : Fin n)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    GateApp gates12 n where
  gate := ⟨1, M.submatrix compiler_single_index compiler_single_index⟩
  mem := ⟨compiler_unitary_submatrix_equiv compiler_single_index M hM, by norm_num, by norm_num⟩
  wires := ⟨fun _ => i, by intro a b _; exact Subsingleton.elim _ _⟩

theorem compiler_one_qubit_placement_matrix {n : ℕ} (i : Fin n)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    embedOp (compiler_one_qubit_placement i M hM).gate.mat
      (compiler_one_qubit_placement i M hM).wires =
    (SuperconductingQC.onQubit i M).submatrix (compiler_binary_index n)
      (compiler_binary_index n) := by
  ext y z
  simp only [compiler_one_qubit_placement, embedOp, Matrix.of_apply,
    Matrix.submatrix_apply, SuperconductingQC.onQubit, compiler_single_index,
    compiler_binary_index_apply, Function.comp_apply]
  have hc : (∀ a : Fin n, a ∉ Set.range (fun _ : Fin 1 => i) → y a = z a) ↔
      (∀ j : Fin n, j ≠ i → finTwoEquiv.symm (y j) = finTwoEquiv.symm (z j)) := by
    simp only [Set.range_const, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq]
  change (if ∀ a : Fin n, a ∉ Set.range (fun _ : Fin 1 => i) → y a = z a then
      M (finTwoEquiv.symm (y i)) (finTwoEquiv.symm (z i)) else 0) =
    (if ∀ j : Fin n, j ≠ i → finTwoEquiv.symm (y j) = finTwoEquiv.symm (z j) then
      M (finTwoEquiv.symm (y i)) (finTwoEquiv.symm (z i)) else 0)
  simp only [hc]

def compiler_pair_index : Qubits 2 ≃ (Fin 2 × Fin 2) where
  toFun x := (finTwoEquiv.symm (x 0), finTwoEquiv.symm (x 1))
  invFun a := ![finTwoEquiv a.1, finTwoEquiv a.2]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv a := by rcases a with ⟨a,b⟩; simp

theorem compiler_cnot_unitary :
    SuperconductingQC.CNOT ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  have hone : (1 + 1 : Fin 2) = 0 := by decide
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [SuperconductingQC.CNOT, Matrix.mul_apply, Matrix.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, hone]

noncomputable def compiler_two_qubit_placement {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    GateApp gates12 n where
  gate := ⟨2, SuperconductingQC.CNOT.submatrix compiler_pair_index compiler_pair_index⟩
  mem := ⟨compiler_unitary_submatrix_equiv compiler_pair_index _ compiler_cnot_unitary,
    by norm_num, by norm_num⟩
  wires := ⟨![i,j], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

theorem compiler_two_qubit_placement_matrix {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    embedOp (compiler_two_qubit_placement i j hij).gate.mat
      (compiler_two_qubit_placement i j hij).wires =
    (SuperconductingQC.onPair i j SuperconductingQC.CNOT).submatrix
      (compiler_binary_index n) (compiler_binary_index n) := by
  ext y z
  change (if ∀ a : Fin n, a ∉ Set.range (![i,j] : Fin 2 → Fin n) → y a = z a then
      SuperconductingQC.CNOT (finTwoEquiv.symm (y i), finTwoEquiv.symm (y j))
        (finTwoEquiv.symm (z i), finTwoEquiv.symm (z j)) else 0) =
    (if ∀ a : Fin n, a ≠ i → a ≠ j →
      finTwoEquiv.symm (y a) = finTwoEquiv.symm (z a) then
      SuperconductingQC.CNOT (finTwoEquiv.symm (y i), finTwoEquiv.symm (y j))
        (finTwoEquiv.symm (z i), finTwoEquiv.symm (z j)) else 0)
  congr 1
  simp [Set.mem_range, Fin.exists_fin_two, eq_comm, and_imp]
  exact ⟨fun h a hi hj => h a hj hi, fun h a hi hj => h a hj hi⟩

theorem compiler_binary_circuit_synthesis (n : ℕ) (hn : 1 ≤ n)
    (W : Matrix.unitaryGroup (Fin n → Fin 2) ℂ) :
    ∃ c : Circuit gates12 n,
      c.unitary = (W : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ).submatrix
        (compiler_binary_index n) (compiler_binary_index n) := by
  have hW : W ∈ Subgroup.closure
      (SuperconductingQC.singleQubitGates n ∪
        SuperconductingQC.twoQubitGateInstances n SuperconductingQC.CNOT) := by
    rw [SuperconductingQC.closure_singleQubit_CNOT_eq_top n hn]
    trivial
  induction hW using Subgroup.closure_induction with
  | mem W hW =>
    rcases hW with hsingle | hpair
    · obtain ⟨i, M, hM, hW⟩ := hsingle
      refine ⟨[compiler_one_qubit_placement i M hM], ?_⟩
      simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      rw [hW]
      exact compiler_one_qubit_placement_matrix i M hM
    · obtain ⟨i, j, hij, hW⟩ := hpair
      refine ⟨[compiler_two_qubit_placement i j hij], ?_⟩
      simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      rw [hW]
      exact compiler_two_qubit_placement_matrix i j hij
  | one =>
    refine ⟨[], ?_⟩
    ext y z
    simp [Circuit.unitary, Matrix.one_apply, (compiler_binary_index n).injective.eq_iff]
  | mul W V _ _ ihW ihV =>
    obtain ⟨c, hc⟩ := ihW
    obtain ⟨d, hd⟩ := ihV
    refine ⟨d ++ c, ?_⟩
    rw [compiler_circuit_append, hc, hd]
    exact Matrix.submatrix_mul_equiv _ _ (compiler_binary_index n)
      (compiler_binary_index n) (compiler_binary_index n)
  | inv W _ ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨compiler_adjoint_circuit c, ?_⟩
    rw [compiler_circuit_adjoint, hc]
    rfl

/-- Every finite qubit unitary has an exact realization with arbitrary
one-qubit and two-qubit gates, with no oracle calls. -/
theorem compiler_exact_circuit_synthesis (n : ℕ) (hn : 1 ≤ n)
    (M : Matrix (Qubits n) (Qubits n) ℂ) (hM : M ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ∃ c : Circuit gates12 n, c.unitary = M := by
  let e := compiler_binary_index n
  let W : Matrix.unitaryGroup (Fin n → Fin 2) ℂ :=
    ⟨M.submatrix e.symm e.symm, compiler_unitary_submatrix_equiv e.symm M hM⟩
  obtain ⟨c, hc⟩ := compiler_binary_circuit_synthesis n hn W
  refine ⟨c, hc.trans ?_⟩
  ext y z
  simp [W, e, Matrix.submatrix_apply]

set_option autoImplicit false

open QAlgorithms QuantumLTF.Majority

/-- Append the |-> answer qubit used to turn the Boolean oracle into a phase oracle. -/
noncomputable def compiler_phase_lift {n : ℕ} (x : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits (n+1)) :=
  WithLp.toLp 2 (fun y =>
    (if y (Fin.last n) then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
      x (fun i => y i.castSucc))

/-- A single Majority bit-oracle call acts by phase kickback on the data register. -/
theorem compiler_majority_phase_kickback {n : ℕ} (A : Finset (Fin n))
    (x : EuclideanSpace ℂ (Qubits n)) (y : Qubits (n+1)) :
    act (majorityOracle A) (compiler_phase_lift x) y =
      (if majorityBit A (fun i => y i.castSucc) then (-1 : ℂ) else 1) *
        compiler_phase_lift x y := by
  classical
  let b := majorityBit A (fun i => y i.castSucc)
  let z : Qubits (n+1) := Fin.snoc (fun i => y i.castSucc) (xor (y (Fin.last n)) b)
  have hhead (i : Fin n) : z i.castSucc = y i.castSucc := by simp [z]
  have hlast : z (Fin.last n) = xor (y (Fin.last n)) b := by simp [z]
  have hb : majorityBit A (fun i => z i.castSucc) = b := by simp [hhead, b]
  have hxor : y (Fin.last n) = xor (z (Fin.last n))
      (majorityBit A (fun i => z i.castSucc)) := by
    rw [hlast, hb]
    cases y (Fin.last n) <;> cases b <;> rfl
  have hunique (w : Qubits (n+1))
      (hh : (∀ i : Fin n, y i.castSucc = w i.castSucc) ∧
        y (Fin.last n) = xor (w (Fin.last n)) (majorityBit A (fun i => w i.castSucc))) :
      w = z := by
    have hwhead : (fun i : Fin n => w i.castSucc) = (fun i => y i.castSucc) :=
      funext (fun i => (hh.1 i).symm)
    have hwbit : majorityBit A (fun i => w i.castSucc) = b := by rw [hwhead]
    have hwlast : w (Fin.last n) = xor (y (Fin.last n)) b := by
      have hh' := hh.2
      rw [hwbit] at hh'
      cases hw : w (Fin.last n) <;> cases hy : y (Fin.last n) <;>
        cases hb' : b <;> simp [hw, hy, hb'] at hh' ⊢
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hwlast, hlast]
    · exact (hh.1 j).symm.trans (hhead j).symm
  change (∑ w : Qubits (n+1), majorityOracle A y w * compiler_phase_lift x w) = _
  rw [Finset.sum_eq_single z]
  · rw [majorityOracle, Matrix.of_apply, if_pos ⟨fun i => (hhead i).symm, hxor⟩, one_mul]
    change (if z (Fin.last n) then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
        x (fun i => z i.castSucc) =
      (if b then (-1 : ℂ) else 1) *
        ((if y (Fin.last n) then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
          x (fun i => y i.castSucc))
    simp only [hhead, hlast]
    cases y (Fin.last n) <;> cases b <;> simp
  · intro w _ hw
    have hnot : ¬ ((∀ i : Fin n, y i.castSucc = w i.castSucc) ∧
        y (Fin.last n) = xor (w (Fin.last n)) (majorityBit A (fun i => w i.castSucc))) :=
      fun hh => hw (hunique w hh)
    simp only [majorityOracle, Matrix.of_apply, if_neg hnot, zero_mul]
  · simp

theorem compiler_phase_lift_norm {n : ℕ} (x : EuclideanSpace ℂ (Qubits n)) :
    ‖compiler_phase_lift x‖ = ‖x‖ := by
  have hcoeff : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 = (1/2 : ℝ) := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsq : ‖compiler_phase_lift x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n+1) => Bool))]
    rw [Fintype.sum_prod_type]
    simp [Fin.snocEquiv, Fintype.sum_bool, compiler_phase_lift,
      norm_mul, mul_pow, hcoeff]
    simp only [← Finset.mul_sum]
    ring
  nlinarith [norm_nonneg (compiler_phase_lift x), norm_nonneg x]

/-- The physical one-query block used for phase kickback. -/
def compiler_single_majority_query (n : ℕ) :
    OracleCircuit QuantumLTF.Membership.gates12 (fun _ : Fin 1 => n+1) (n+1) :=
  [.query 0 false none (Function.Embedding.refl _) (by simp)]

theorem compiler_single_majority_query_count (n : ℕ) :
    (compiler_single_majority_query n).queryCount 0 = 1 := by
  simp [compiler_single_majority_query, OracleCircuit.queryCount, OracleStep.IsQueryTo]

theorem compiler_single_majority_query_unitary {n : ℕ} (A : Finset (Fin n)) :
    (compiler_single_majority_query n).unitary (fun _ => majorityOracle A) =
      majorityOracle A := by
  simp only [compiler_single_majority_query, OracleCircuit.unitary, List.map_cons,
    List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.prod_cons, List.prod_nil, mul_one, OracleStep.mat, Bool.false_eq_true, ite_false]
  ext y z
  simp [embedOp]
  rfl

/-- Exact one-query phase simulation with a norm-preserving answer-qubit embedding. -/
theorem compiler_single_query_phase_simulation {n : ℕ} (A : Finset (Fin n))
    (x : EuclideanSpace ℂ (Qubits n)) :
    (compiler_single_majority_query n).queryCount 0 = 1 ∧
    ‖compiler_phase_lift x‖ = ‖x‖ ∧
    ∀ y : Qubits (n+1),
      act ((compiler_single_majority_query n).unitary (fun _ => majorityOracle A))
        (compiler_phase_lift x) y =
      (if majorityBit A (fun i => y i.castSucc) then (-1 : ℂ) else 1) *
        compiler_phase_lift x y := by
  refine ⟨compiler_single_majority_query_count n, compiler_phase_lift_norm x, ?_⟩
  intro y
  rw [compiler_single_majority_query_unitary]
  exact compiler_majority_phase_kickback A x y

/-- The phase-kickback encoding is a complex-linear isometry, so arbitrary
unitaries on the data register can be transported through it. -/
noncomputable def compiler_phase_embedding (n : ℕ) :
    EuclideanSpace ℂ (Qubits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Qubits (n+1)) where
  toFun := compiler_phase_lift
  map_add' x y := by
    ext z
    simp [compiler_phase_lift, mul_add]
  map_smul' r x := by
    ext z
    simp [compiler_phase_lift, mul_left_comm]
  norm_map' := compiler_phase_lift_norm

/-- The physical circuit intertwines the answer-qubit encoding with the
abstract unitary phase oracle used in the proved adversary algorithm. -/
theorem compiler_query_intertwines_abstract_phase {n : ℕ} (A : Finset (Fin n))
    (x : EuclideanSpace ℂ (Qubits n)) :
    act ((compiler_single_majority_query n).unitary (fun _ => majorityOracle A))
        (compiler_phase_embedding n x) =
      compiler_phase_embedding n (compiler_sign_oracle (majorityBit A) x) := by
  ext y
  rw [compiler_single_majority_query_unitary]
  change act (majorityOracle A) (compiler_phase_lift x) y = _
  rw [compiler_majority_phase_kickback]
  change (if majorityBit A (fun i => y i.castSucc) then (-1 : ℂ) else 1) *
      ((if y (Fin.last n) then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
        x (fun i => y i.castSucc)) =
    (if y (Fin.last n) then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
      ((if majorityBit A (fun i => y i.castSucc) then (-1 : ℂ) else 1) *
        x (fun i => y i.castSucc))
  ring

set_option autoImplicit false

open QAlgorithms QuantumLTF.Majority

/-- Isometrically encode an orthonormal coordinate basis along any finite injection. -/
noncomputable def compiler_basis_embedding {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) :
    EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ β := by
  let L : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ β :=
    { toFun := fun x => ∑ i, x i • EuclideanSpace.single (e i) (1 : ℂ)
      map_add' := by
        intro x y
        change (∑ i, (x i + y i) • EuclideanSpace.single (e i) (1 : ℂ)) = _
        simp only [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        change (∑ i, (r * x i) • EuclideanSpace.single (e i) (1 : ℂ)) = _
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_smul r (x i) _ }
  apply L.isometryOfInner
  intro x y
  change inner ℂ (∑ i, x i • EuclideanSpace.single (e i) (1 : ℂ))
    (∑ i, y i • EuclideanSpace.single (e i) (1 : ℂ)) = inner ℂ x y
  simp [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, e.injective.eq_iff,
    PiLp.inner_apply, RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc]

@[simp] theorem compiler_basis_embedding_single {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) (i : α) :
    compiler_basis_embedding e (EuclideanSpace.single i 1) =
      EuclideanSpace.single (e i) 1 := by
  simp [compiler_basis_embedding, PiLp.single_apply]

/-- One-hot auxiliary code makes the basis encoding injective without
requiring any bound on the number of clean ancilla qubits. -/
noncomputable def compiler_one_hot {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Qubits (Fintype.card α) := fun i => decide (i = Fintype.equivFin α a)

theorem compiler_one_hot_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (compiler_one_hot (α := α)) := by
  intro a b hab
  have hh := congrFun hab (Fintype.equivFin α a)
  simp only [compiler_one_hot, decide_true, decide_eq_true_eq] at hh
  exact (Fintype.equivFin α).injective (of_decide_eq_true hh.symm)

abbrev CompilerClockIndex (n k N : ℕ) (ω : Type) :=
  (Fin N × Option (BoundedSupports n k)) ⊕ (Qubits n × ω)

def compiler_index_query {n k N : ℕ} {ω : Type} : CompilerClockIndex n k N ω → Qubits n
  | .inl _ => fun _ => false
  | .inr (s, _) => s

def compiler_index_control {n k N : ℕ} {ω : Type} : CompilerClockIndex n k N ω → Bool
  | .inl _ => false
  | .inr _ => true

def compiler_index_output {n k N : ℕ} {ω : Type} : CompilerClockIndex n k N ω → Qubits n
  | .inl (_, some A) => fun i => decide (i ∈ A.1)
  | _ => fun _ => false

abbrev CompilerDataQubits (n k N : ℕ) (ω : Type) [Fintype ω] :=
  n + ((n + Fintype.card (CompilerClockIndex n k N ω)) + 1)

/-- The data encoding places query wires first, followed by the query-control
bit, the measured characteristic-vector wires, and a one-hot auxiliary code. -/
noncomputable def compiler_encode_basis {n k N : ℕ} {ω : Type} [Fintype ω] [DecidableEq ω]
    (a : CompilerClockIndex n k N ω) : Qubits (CompilerDataQubits n k N ω) :=
  Fin.append (compiler_index_query a)
    (Fin.cons (compiler_index_control a)
      (Fin.append (compiler_index_output a) (compiler_one_hot a)))

theorem compiler_encode_basis_injective {n k N : ℕ} {ω : Type} [Fintype ω] [DecidableEq ω] :
    Function.Injective (compiler_encode_basis (n := n) (k := k) (N := N) (ω := ω)) := by
  intro a b hab
  apply compiler_one_hot_injective
  funext i
  have hh := congrFun hab (Fin.natAdd n (Fin.succ (Fin.natAdd n i)))
  simpa [compiler_encode_basis] using hh

noncomputable def compiler_clock_basis_embedding {n k N : ℕ} {ω : Type} [Fintype ω] [DecidableEq ω] :
    EuclideanSpace ℂ (CompilerClockIndex n k N ω) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Qubits (CompilerDataQubits n k N ω)) :=
  compiler_basis_embedding ⟨compiler_encode_basis, compiler_encode_basis_injective⟩

def compiler_query_wire {n k N : ℕ} {ω : Type} [Fintype ω] (i : Fin n) :
    Fin (CompilerDataQubits n k N ω + 1) :=
  (i.castAdd ((n + Fintype.card (CompilerClockIndex n k N ω)) + 1)).castSucc

def compiler_control_wire (n k N : ℕ) (ω : Type) [Fintype ω] :
    Fin (CompilerDataQubits n k N ω + 1) :=
  (Fin.natAdd n (0 : Fin ((n + Fintype.card (CompilerClockIndex n k N ω)) + 1))).castSucc

def compiler_output_wire {n k N : ℕ} {ω : Type} [Fintype ω] (i : Fin n) :
    Fin (CompilerDataQubits n k N ω + 1) :=
  (Fin.natAdd n (Fin.succ (i.castAdd (Fintype.card (CompilerClockIndex n k N ω))))).castSucc

def compiler_query_wires (n k N : ℕ) (ω : Type) [Fintype ω] :
    Fin (n+1) ↪ Fin (CompilerDataQubits n k N ω + 1) where
  toFun := Fin.snoc compiler_query_wire (Fin.last _)
  inj' := by
    apply Fin.snoc_injective_iff.mpr
    constructor
    · intro i j hij
      have hv := congrArg Fin.val hij
      exact Fin.ext hv
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      simp [compiler_query_wire, CompilerDataQubits] at hv
      have := i.isLt
      omega

theorem compiler_control_not_query (n k N : ℕ) (ω : Type) [Fintype ω] :
    compiler_control_wire n k N ω ∉ Set.range (compiler_query_wires n k N ω) := by
  rintro ⟨i, hi⟩
  revert hi
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro hi
    have hv := congrArg Fin.val hi
    simp [compiler_query_wires, compiler_control_wire, CompilerDataQubits] at hv
  · intro hi
    have hv := congrArg Fin.val hi
    simp [compiler_query_wires, compiler_query_wire, compiler_control_wire] at hv
    have := j.isLt
    omega

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open QAlgorithms QuantumLTF.Membership

theorem compiler_act_mul {α : Type*} [Fintype α]
    (M L : Matrix α α ℂ) (x : EuclideanSpace ℂ α) :
    act (M * L) x = act M (act L x) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec x.ofLp M L).symm

theorem compiler_act_add {α : Type*} [Fintype α]
    (M : Matrix α α ℂ) (x y : EuclideanSpace ℂ α) :
    act M (x+y) = act M x + act M y := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]

theorem compiler_act_smul {α : Type*} [Fintype α]
    (M : Matrix α α ℂ) (c : ℂ) (x : EuclideanSpace ℂ α) :
    act M (c • x) = c • act M x := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

theorem compiler_act_sum {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α α ℂ) (x : β → EuclideanSpace ℂ α) :
    act M (∑ i, x i) = ∑ i, act M (x i) := by
  classical
  exact map_sum (Matrix.toEuclideanCLM (n := α) (𝕜 := ℂ) M) x Finset.univ

theorem compiler_act_unitary_matrix {n : ℕ}
    (V : EuclideanSpace ℂ (Qubits n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Qubits n))
    (x : EuclideanSpace ℂ (Qubits n)) :
    act (V.toMatrix (EuclideanSpace.basisFun _ _).toBasis
      (EuclideanSpace.basisFun _ _).toBasis) x = V x := by
  ext i
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Qubits n) ℂ).toBasis
    (EuclideanSpace.basisFun (Qubits n) ℂ).toBasis V.toLinearMap x
  exact congrFun h i

theorem compiler_synthesize_isometry (n : ℕ) (hn : 1 ≤ n)
    (V : EuclideanSpace ℂ (Qubits n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Qubits n)) :
    ∃ c : Circuit gates12 n, ∀ x, act c.unitary x = V x := by
  let b := EuclideanSpace.basisFun (Qubits n) ℂ
  obtain ⟨c, hc⟩ := compiler_exact_circuit_synthesis n hn
    (V.toMatrix b.toBasis b.toBasis) (V.toMatrix_mem_unitaryGroup b b)
  refine ⟨c, fun x => ?_⟩
  rw [hc]
  exact compiler_act_unitary_matrix V x

theorem compiler_prepare_unit_vector {n : ℕ} (hn : 1 ≤ n)
    (x : EuclideanSpace ℂ (Qubits n)) (hx : ‖x‖ = 1) :
    ∃ c : Circuit gates12 n, act c.unitary (zeroKet n) = x := by
  classical
  let f : ℂ →ₗ[ℂ] EuclideanSpace ℂ (Qubits n) :=
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (zeroKet n)
  let g : ℂ →ₗ[ℂ] EuclideanSpace ℂ (Qubits n) :=
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight x
  obtain ⟨V, hV⟩ := compiler_exists_workspace_unitary f g (by
    intro c
    simp [f, g, norm_smul, hx, zeroKet, ket])
  obtain ⟨c, hc⟩ := compiler_synthesize_isometry n hn V
  refine ⟨c, (hc _).trans ?_⟩
  simpa [f, g] using hV 1

def compiler_plain_circuit {r n : ℕ} {a : Fin r → ℕ}
    (c : Circuit gates12 n) : OracleCircuit gates12 a n := c.map OracleStep.gate

theorem compiler_plain_circuit_unitary {r n : ℕ} {a : Fin r → ℕ}
    (c : Circuit gates12 n) (orc : (j : Fin r) → Matrix (Qubits (a j)) (Qubits (a j)) ℂ) :
    (compiler_plain_circuit c).unitary orc = c.unitary := by
  simp [compiler_plain_circuit, OracleCircuit.unitary, Circuit.unitary, List.map_map,
    Function.comp_def, OracleStep.mat]

theorem compiler_plain_circuit_count {r n : ℕ} {a : Fin r → ℕ}
    (c : Circuit gates12 n) (j : Fin r) :
    (compiler_plain_circuit (a := a) c).queryCount j = 0 := by
  simp [compiler_plain_circuit, OracleCircuit.queryCount, List.countP_map,
    Function.comp_def, OracleStep.IsQueryTo]

theorem compiler_oracle_append {r n : ℕ} {a : Fin r → ℕ}
    (c d : OracleCircuit gates12 a n)
    (orc : (j : Fin r) → Matrix (Qubits (a j)) (Qubits (a j)) ℂ) :
    (c++d).unitary orc = d.unitary orc * c.unitary orc := by
  simp [OracleCircuit.unitary, List.reverse_append, List.prod_append]

theorem compiler_oracle_append_count {r n : ℕ} {a : Fin r → ℕ}
    (c d : OracleCircuit gates12 a n) (j : Fin r) :
    (c++d).queryCount j = c.queryCount j + d.queryCount j := by
  exact List.countP_append

def compiler_query_schedule {r m : ℕ} {a : Fin r → ℕ}
    (initial : Circuit gates12 m) (Q : OracleCircuit gates12 a m)
    (steps : ℕ → Circuit gates12 m) : ℕ → OracleCircuit gates12 a m
  | 0 => compiler_plain_circuit initial
  | t+1 => compiler_query_schedule initial Q steps t ++ Q ++ compiler_plain_circuit (steps t)

theorem compiler_query_schedule_count {r m : ℕ} {a : Fin r → ℕ}
    (initial : Circuit gates12 m) (Q : OracleCircuit gates12 a m)
    (steps : ℕ → Circuit gates12 m) (j : Fin r) (hQ : Q.queryCount j = 1) (t : ℕ) :
    (compiler_query_schedule initial Q steps t).queryCount j = t := by
  induction t with
  | zero => exact compiler_plain_circuit_count _ _
  | succ t ih =>
    simp only [compiler_query_schedule, compiler_oracle_append_count, ih, hQ,
      compiler_plain_circuit_count, add_zero]

theorem compiler_query_schedule_run {r m : ℕ} {a : Fin r → ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (J : E →ₗᵢ[ℂ] EuclideanSpace ℂ (Qubits m))
    (U : ℕ → E ≃ₗᵢ[ℂ] E) (O : E ≃ₗᵢ[ℂ] E) (start : E)
    (initial : Circuit gates12 m) (Q : OracleCircuit gates12 a m)
    (steps : ℕ → Circuit gates12 m)
    (orc : (j : Fin r) → Matrix (Qubits (a j)) (Qubits (a j)) ℂ)
    (hinit : act initial.unitary (zeroKet m) = J start)
    (hQ : ∀ x, act (Q.unitary orc) (J x) = J (O x))
    (hstep : ∀ t x, act (steps t).unitary (J x) = J (U t x)) (t : ℕ) :
    act ((compiler_query_schedule initial Q steps t).unitary orc) (zeroKet m) =
      J (compiler_clock_run U O t start) := by
  induction t with
  | zero => simpa [compiler_query_schedule, compiler_plain_circuit_unitary, compiler_clock_run]
      using hinit
  | succ t ih =>
    simp only [compiler_query_schedule, compiler_oracle_append, compiler_act_mul,
      compiler_plain_circuit_unitary, ih, hQ, hstep]
    rfl

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open QAlgorithms QuantumLTF.Majority QuantumLTF.Membership

theorem compiler_act_single {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℂ) (z : α) (y : α) :
    act M (EuclideanSpace.single z 1) y = M y z := by
  simp [act, Matrix.mulVec, dotProduct, PiLp.single_apply]

theorem compiler_embedded_column {r m : ℕ}
    (M : Matrix (Qubits r) (Qubits r) ℂ) (w : Fin r ↪ Fin m)
    (z z' : Qubits m)
    (hrest : ∀ i, i ∉ Set.range w → z' i = z i)
    (hcol : ∀ v, M v (z ∘ w) = if v = z' ∘ w then 1 else 0) :
    act (embedOp M w) (EuclideanSpace.single z 1) = EuclideanSpace.single z' 1 := by
  classical
  ext y
  rw [compiler_act_single, embedOp, Matrix.of_apply, hcol]
  by_cases hy : y = z'
  · subst y
    rw [if_pos hrest]
    simp [PiLp.single_apply]
  · have hbad : ¬ ((∀ i, i ∉ Set.range w → y i = z i) ∧ y ∘ w = z' ∘ w) := by
      rintro ⟨hr, hw⟩
      apply hy
      funext i
      by_cases hi : i ∈ Set.range w
      · obtain ⟨j, rfl⟩ := hi
        exact congrFun hw j
      · exact (hr i hi).trans (hrest i hi).symm
    simp only [PiLp.single_apply, hy, if_false]
    split_ifs with hr hw
    · exact (hbad ⟨hr, hw⟩).elim
    · rfl
    · rfl

theorem compiler_controlled_majority_column {n : ℕ} (A : Finset (Fin n))
    (s : Qubits n) (b c : Bool) (y : Qubits ((n+1)+1)) :
    controlledQubits (majorityOracle A) y (Fin.cons c (Fin.snoc s b)) =
      if y = Fin.cons c (Fin.snoc s (xor b (c && majorityBit A s))) then 1 else 0 := by
  classical
  have heq (d : Bool) : y = Fin.cons c (Fin.snoc s d) ↔
      y 0 = c ∧ (∀ i : Fin n, y i.castSucc.succ = s i) ∧
        y (Fin.last n).succ = d := by
    constructor
    · intro h
      subst y
      simp
    · rintro ⟨hc, hs, hb⟩
      funext i
      refine Fin.cases hc (fun j => ?_) i
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hb
      · simpa using hs j
  have htail : Fin.tail y = Fin.snoc s b ↔
      (∀ i : Fin n, y i.castSucc.succ = s i) ∧ y (Fin.last n).succ = b := by
    constructor
    · intro h
      exact ⟨fun i => by simpa [Fin.tail] using congrFun h i.castSucc,
        by simpa [Fin.tail] using congrFun h (Fin.last n)⟩
    · rintro ⟨hs, hb⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [Fin.tail] using hb
      · simpa [Fin.tail] using hs j
  cases c <;>
    simp only [controlledQubits, Matrix.submatrix_apply, controlled, Matrix.of_apply,
      Fin.cons_zero, Fin.tail_cons, Matrix.one_apply, majorityOracle,
      Fin.snoc_castSucc, Fin.snoc_last, Bool.false_and, Bool.true_and, Bool.xor_false,
      heq, htail]
  · by_cases hc : y 0 = false
    · simp [hc]
    · simp [hc]
  · by_cases hc : y 0 = true
    · simp [hc, Fin.tail]
      rfl
    · simp [hc]

def compiler_controlled_query (n k N : ℕ) (ω : Type) [Fintype ω] :
    OracleCircuit gates12 (fun _ : Fin 1 => n+1) (CompilerDataQubits n k N ω +1) :=
  [.query 0 false (some (compiler_control_wire n k N ω)) (compiler_query_wires n k N ω)
    (by intro c hc; cases Option.some.inj hc; exact compiler_control_not_query n k N ω)]

theorem compiler_controlled_query_count (n k N : ℕ) (ω : Type) [Fintype ω] :
    (compiler_controlled_query n k N ω).queryCount 0 = 1 := by
  simp [compiler_controlled_query, OracleCircuit.queryCount, OracleStep.IsQueryTo]

theorem compiler_controlled_query_basis {n k N : ℕ} {ω : Type} [Fintype ω] [DecidableEq ω]
    (A : Finset (Fin n)) (a : CompilerClockIndex n k N ω) (b : Bool) :
    act ((compiler_controlled_query n k N ω).unitary (fun _ => majorityOracle A))
      (EuclideanSpace.single (Fin.snoc (compiler_encode_basis a) b) 1) =
    EuclideanSpace.single (Fin.snoc (compiler_encode_basis a)
      (xor b (compiler_index_control a && majorityBit A (compiler_index_query a)))) 1 := by
  classical
  simp only [compiler_controlled_query, OracleCircuit.unitary, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil,
    mul_one, OracleStep.mat, Bool.false_eq_true, if_false]
  apply compiler_embedded_column
  · intro i hi
    induction i using Fin.lastCases with
    | last =>
      exact (hi ⟨(Fin.last n).succ, by simp [compiler_query_wires]⟩).elim
    | cast i => simp
  · intro v
    have hloc (d : Bool) :
        Fin.snoc (compiler_encode_basis a) d ∘
          Fin.cons (compiler_control_wire n k N ω) (compiler_query_wires n k N ω) =
        Fin.cons (compiler_index_control a) (Fin.snoc (compiler_index_query a) d) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Function.comp_apply, Fin.cons_zero, compiler_control_wire,
          Fin.snoc_castSucc]
        simp [compiler_encode_basis]
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [compiler_query_wires]
        · simp [compiler_query_wires, compiler_query_wire, compiler_encode_basis]
    change controlledQubits (majorityOracle A) v
      (Fin.snoc (compiler_encode_basis a) b ∘
        Fin.cons (compiler_control_wire n k N ω) (compiler_query_wires n k N ω)) =
      if v = Fin.snoc (compiler_encode_basis a)
        (xor b (compiler_index_control a && majorityBit A (compiler_index_query a))) ∘
        Fin.cons (compiler_control_wire n k N ω) (compiler_query_wires n k N ω) then 1 else 0
    rw [hloc, hloc]
    exact compiler_controlled_majority_column A _ _ _ _

theorem compiler_phase_embedding_single {n : ℕ} (s : Qubits n) :
    compiler_phase_embedding n (EuclideanSpace.single s 1) =
      ((Real.sqrt 2)⁻¹ : ℂ) • EuclideanSpace.single (Fin.snoc s false) 1 +
      (-((Real.sqrt 2)⁻¹ : ℂ)) • EuclideanSpace.single (Fin.snoc s true) 1 := by
  classical
  ext y
  have hy : Fin.snoc (fun i => y i.castSucc) (y (Fin.last n)) = y :=
    Fin.snoc_init_self y
  conv_rhs => rw [← hy]
  simp only [compiler_phase_embedding, LinearIsometry.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, compiler_phase_lift, WithLp.ofLp_toLp, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, Fin.snoc_inj]
  by_cases hs : (fun i => y i.castSucc) = s
  · cases hb : y (Fin.last n) <;> simp [hs, hb]
  · have hs' : s ≠ (fun i => y i.castSucc) := Ne.symm hs
    cases hb : y (Fin.last n) <;> simp [hs, hs', hb]

noncomputable def compiler_full_embedding {n k N : ℕ} {ω : Type} [Fintype ω] [DecidableEq ω] :
    EuclideanSpace ℂ (CompilerClockIndex n k N ω) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Qubits (CompilerDataQubits n k N ω +1)) :=
  (compiler_phase_embedding _).comp compiler_clock_basis_embedding

theorem compiler_controlled_query_phase_single {n k N : ℕ} {ω : Type}
    [Fintype ω] [DecidableEq ω]
    (A : Finset (Fin n)) (a : CompilerClockIndex n k N ω) :
    act ((compiler_controlled_query n k N ω).unitary (fun _ => majorityOracle A))
      (compiler_full_embedding (EuclideanSpace.single a 1)) =
    (if compiler_index_control a && majorityBit A (compiler_index_query a) then (-1:ℂ) else 1) •
      compiler_full_embedding (EuclideanSpace.single a 1) := by
  change act _ (compiler_phase_embedding _ (compiler_basis_embedding _
    (EuclideanSpace.single a 1))) = _
  simp only [compiler_basis_embedding_single, compiler_phase_embedding_single,
    compiler_act_add, compiler_act_smul, Function.Embedding.coeFn_mk]
  rw [compiler_controlled_query_basis A a false, compiler_controlled_query_basis A a true]
  change _ = (if compiler_index_control a && majorityBit A (compiler_index_query a)
    then (-1:ℂ) else 1) • (compiler_phase_embedding _
      (compiler_basis_embedding _ (EuclideanSpace.single a 1)))
  rw [compiler_basis_embedding_single, compiler_phase_embedding_single]
  cases hb : compiler_index_control a && majorityBit A (compiler_index_query a) <;>
    simp [hb, smul_add, smul_smul, add_comm]

theorem compiler_controlled_query_intertwines {n k N : ℕ} {ω : Type}
    [Fintype ω] [DecidableEq ω] (A : Finset (Fin n))
    (x : EuclideanSpace ℂ (CompilerClockIndex n k N ω)) :
    act ((compiler_controlled_query n k N ω).unitary (fun _ => majorityOracle A))
      (compiler_full_embedding x) =
    compiler_full_embedding (compiler_sign_oracle
      (Sum.elim (fun _ => false) (fun j : Qubits n × ω => majorityBit A j.1)) x) := by
  classical
  have hexp (y : EuclideanSpace ℂ (CompilerClockIndex n k N ω)) :
      y = ∑ a, y a • EuclideanSpace.single a 1 := by
    simpa [EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (CompilerClockIndex n k N ω) ℂ).sum_repr y).symm
  conv_lhs => arg 2; rw [hexp x]
  rw [map_sum, compiler_act_sum]
  simp only [map_smul, compiler_act_smul, compiler_controlled_query_phase_single, smul_smul]
  conv_rhs => arg 2; rw [hexp (compiler_sign_oracle _ x)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul]
  congr 1
  cases a with
  | inl a => simp [compiler_sign_oracle, compiler_index_control]
  | inr a =>
    simp [compiler_sign_oracle, compiler_index_control, compiler_index_query, mul_comm]
    rfl

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open QAlgorithms QuantumLTF.Majority

theorem compiler_clock_start_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) :
    ‖compiler_clock_start (ι := ι) N‖ ^ 2 = N := by
  have hval (j : Fin N) (label : Option ι) :
      compiler_clock_start N (j, label) = if label = none then (1:ℂ) else 0 := by
    simp only [compiler_clock_start, WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply,
      Pi.single_apply, Prod.mk.injEq]
    rw [Finset.sum_eq_single j]
    · simp [eq_comm]
    · intro b _ hb
      simp [hb, Ne.symm hb]
    · simp
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp [hval, Fintype.sum_option]

theorem compiler_normalized_start_norm {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] (N : ℕ) (hN : 0 < N) :
    ‖(((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_left (β := β) (compiler_clock_start (ι := ι) N)‖ = 1 := by
  have hleft : ‖compiler_left (β := β) (compiler_clock_start (ι := ι) N)‖ =
      ‖compiler_clock_start (ι := ι) N‖ := by
    simp [compiler_left, EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  rw [norm_smul, hleft]
  have hs := compiler_clock_start_norm_sq (ι := ι) N
  have hnp : (0:ℝ) < N := by exact_mod_cast hN
  have hnorm : ‖compiler_clock_start (ι := ι) N‖ = Real.sqrt N := by
    nlinarith [Real.sq_sqrt hnp.le, Real.sqrt_nonneg (N:ℝ),
      norm_nonneg (compiler_clock_start (ι := ι) N)]
  rw [hnorm]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (N:ℝ)),
    (Real.sqrt_pos.mpr hnp).ne']

theorem compiler_basis_embedding_apply {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) (x : EuclideanSpace ℂ α) (a : α) :
    compiler_basis_embedding e x (e a) = x a := by
  simp [compiler_basis_embedding, WithLp.ofLp_sum, PiLp.single_apply, Pi.single_apply,
    e.injective.eq_iff]

theorem compiler_full_embedding_apply {n k N : ℕ} {ω : Type} [Fintype ω] [DecidableEq ω]
    (x : EuclideanSpace ℂ (CompilerClockIndex n k N ω)) (a : CompilerClockIndex n k N ω)
    (b : Bool) :
    compiler_full_embedding x (Fin.snoc (compiler_encode_basis a) b) =
      (if b then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) * x a := by
  change compiler_phase_lift (compiler_clock_basis_embedding x)
    (Fin.snoc (compiler_encode_basis a) b) = _
  simp only [compiler_phase_lift, WithLp.ofLp_toLp]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change (if b then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) *
    compiler_basis_embedding _ x (compiler_encode_basis a) = _
  have hb := compiler_basis_embedding_apply
    (⟨compiler_encode_basis, compiler_encode_basis_injective⟩ :
      CompilerClockIndex n k N ω ↪ Qubits (CompilerDataQubits n k N ω)) x a
  exact congrArg (fun z => (if b then -((Real.sqrt 2)⁻¹ : ℂ)
    else ((Real.sqrt 2)⁻¹ : ℂ)) * z) hb

def compiler_output_wires (n k N : ℕ) (ω : Type) [Fintype ω] :
    Fin n ↪ Fin (CompilerDataQubits n k N ω +1) where
  toFun := compiler_output_wire
  inj' := by
    intro i j hij
    have hv := congrArg Fin.val hij
    simp only [compiler_output_wire, Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ,
      Fin.val_castAdd] at hv
    apply Fin.ext
    omega

theorem compiler_encoded_success_output {n k N : ℕ} {ω : Type}
    [Fintype ω] [DecidableEq ω] (A : BoundedSupports n k)
    (a : CompilerClockIndex n k N ω) (b : Bool) (ha : compiler_success_event A a) :
    ∀ i : Fin n, (Fin.snoc (compiler_encode_basis a) b :
      Qubits (CompilerDataQubits n k N ω +1)) (compiler_output_wires n k N ω i) =
      decide (i ∈ A.1) := by
  intro i
  cases a with
  | inr a => exact ha.elim
  | inl a =>
    rcases a with ⟨j, label⟩
    change label = some A at ha
    subst label
    change (Fin.snoc (α := fun _ => Bool)
      (compiler_encode_basis (n:=n) (k:=k) (N:=N) (ω:=ω) (.inl (j, some A))) b)
      ((Fin.natAdd n (Fin.succ (i.castAdd
        (Fintype.card (CompilerClockIndex n k N ω))))).castSucc) = _
    rw [Fin.snoc_castSucc]
    simp [compiler_encode_basis, compiler_index_output]

theorem compiler_measurement_lower_bound {n k N : ℕ} {ω : Type}
    [Fintype ω] [DecidableEq ω] (A : BoundedSupports n k)
    (x : EuclideanSpace ℂ (CompilerClockIndex n k N ω)) :
    (∑ a, if compiler_success_event A a then ‖x a‖ ^ 2 else 0) ≤
    probEvent (compiler_full_embedding x)
      (fun z => ∀ i : Fin n, z (compiler_output_wires n k N ω i) = decide (i ∈ A.1)) := by
  classical
  let e : CompilerClockIndex n k N ω × Bool →
      Qubits (CompilerDataQubits n k N ω +1) :=
    fun p => Fin.snoc (compiler_encode_basis p.1) p.2
  have he : Function.Injective e := by
    intro p q hpq
    obtain ⟨ha, hb⟩ := Fin.snoc_inj.mp hpq
    exact Prod.ext (compiler_encode_basis_injective ha) hb
  let P := fun z : Qubits (CompilerDataQubits n k N ω +1) =>
    ∀ i : Fin n, z (compiler_output_wires n k N ω i) = decide (i ∈ A.1)
  let f := fun z => if P z then ‖compiler_full_embedding x z‖ ^ 2 else 0
  have hnonneg (z) : 0 ≤ f z := by dsimp [f]; split_ifs <;> positivity
  have hsub : Finset.univ.image e ⊆ (Finset.univ : Finset (Qubits
      (CompilerDataQubits n k N ω +1))) := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hnonneg z)
  rw [Finset.sum_image (fun p _ q _ hpq => he hpq)] at hle
  have hterm : (∑ p : CompilerClockIndex n k N ω × Bool,
      if compiler_success_event A p.1 then ‖compiler_full_embedding x (e p)‖ ^ 2 else 0) ≤
      ∑ p : CompilerClockIndex n k N ω × Bool, f (e p) := by
    apply Finset.sum_le_sum
    intro p _
    by_cases hp : compiler_success_event A p.1
    · have hP : P (e p) := compiler_encoded_success_output A p.1 p.2 hp
      simp [hp, f, hP]
    · simp only [if_neg hp]
      exact hnonneg _
  have hcoeff : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 = (1/2 : ℝ) := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hmass : (∑ p : CompilerClockIndex n k N ω × Bool,
      if compiler_success_event A p.1 then ‖compiler_full_embedding x (e p)‖ ^ 2 else 0) =
      ∑ a, if compiler_success_event A a then ‖x a‖ ^ 2 else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : compiler_success_event A a <;>
      simp [e, Fintype.sum_bool, ha, compiler_full_embedding_apply, norm_mul, mul_pow, hcoeff]
    ring
  rw [hmass] at hterm
  apply (hterm.trans hle).trans_eq
  simp [f, P, probEvent, prob, ket, EuclideanSpace.inner_single_left, Finset.sum_filter]

set_option autoImplicit false

open QAlgorithms QuantumLTF.Majority QuantumLTF.Membership

/-- Realize the finite phase-query learner by the explicit oracle-circuit
model, preserving the query count and its success probability. -/
theorem solution (n k N : ℕ) (ω : Type) [Fintype ω]
    (hN : 0 < N) :
    let ι := BoundedSupports n k
    let E := EuclideanSpace ℂ ((Fin N × Option ι) ⊕ (Qubits n × ω))
    let O : ι → E ≃ₗᵢ[ℂ] E := fun A => compiler_sign_oracle
      (Sum.elim (fun _ => false) (fun j : Qubits n × ω => majorityBit A.1 j.1))
    let start : E := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_left (compiler_clock_start N)
    ∀ U : ℕ → E ≃ₗᵢ[ℂ] E,
      (∀ A, (∑ j, if compiler_success_event A j then
        ‖compiler_clock_run U (O A) N start j‖ ^ 2 else 0) ≥ (2/3 : ℝ)) →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m)
        (out : Fin n ↪ Fin m), c.queryCount 0 ≤ N ∧ LearnsUpTo (k:=k) c out (2/3) := by
  classical
  dsimp only
  intro U hU
  let E := EuclideanSpace ℂ (CompilerClockIndex n k N ω)
  let J : E →ₗᵢ[ℂ] EuclideanSpace ℂ (Qubits (CompilerDataQubits n k N ω +1)) :=
    compiler_full_embedding
  let start : E := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • compiler_left (compiler_clock_start N)
  have hstart : ‖J start‖ = 1 := by
    rw [J.norm_map]
    exact compiler_normalized_start_norm N hN
  obtain ⟨initial, hinit⟩ := compiler_prepare_unit_vector (by omega) (J start) hstart
  have hex (t : ℕ) : ∃ c : Circuit gates12 (CompilerDataQubits n k N ω +1),
      ∀ x : E, act c.unitary (J x) = J (U t x) := by
    obtain ⟨V, hV⟩ := compiler_transport_unitary J (U t)
    obtain ⟨c, hc⟩ := compiler_synthesize_isometry _ (by omega) V
    exact ⟨c, fun x => (hc (J x)).trans (hV x)⟩
  choose steps hsteps using hex
  let Q := compiler_controlled_query n k N ω
  let c := compiler_query_schedule initial Q steps N
  refine ⟨CompilerDataQubits n k N ω +1, c, compiler_output_wires n k N ω, ?_, ?_⟩
  · exact (compiler_query_schedule_count initial Q steps 0
      (compiler_controlled_query_count n k N ω) N).le
  · intro A hA hk
    let a : BoundedSupports n k := ⟨A, hA, hk⟩
    have hrun := compiler_query_schedule_run J U
      (compiler_sign_oracle (Sum.elim (fun _ => false)
        (fun j : Qubits n × ω => majorityBit A j.1))) start initial Q steps
      (fun _ => majorityOracle A) hinit (compiler_controlled_query_intertwines A) hsteps N
    change probEvent (act (c.unitary (fun _ => majorityOracle A)) (zeroKet _)) _ ≥ _
    rw [hrun]
    exact (hU a).trans (compiler_measurement_lower_bound a _)

-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.CertificateBlockCorrectness.hadamard_transports
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:45:47.349187+00:00
-- url     : https://prove2.me/submissions/f077a055-c256-439f-a3fc-edd6fde77d52

/- Generated from Solutions.CertificateQuantumTransports by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Theorems.Thm_QMAPerfectCompleteness_Main_BlockHadamardCoordinates_spectator_mask

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates

/- Inline helpers retained from Solutions.IndexHadamards. -/
section


/-! Paired physical Hadamards and the little-endian index Hadamard matrix. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
namespace QMAPerfectCompleteness.Main.IndexHadamards
open ReversibleGadgets ComparisonCircuits ClockCircuits



lemma piMatrix_one {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α] :
    piMatrix (fun _ : J => (1 : Matrix α α ℂ)) = 1 := by
  classical
  ext y x
  by_cases hxy : y = x
  · subst y
    simp [piMatrix]
  · have hne : ∃ j, y j ≠ x j := by simpa only [funext_iff, not_forall] using hxy
    obtain ⟨j,hj⟩ := hne
    simp only [Matrix.one_apply, if_neg hxy]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Matrix.one_apply, hj]

lemma piMatrix_mul {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α]
    (M N : J → Matrix α α ℂ) :
    piMatrix (fun j => M j * N j) = piMatrix M * piMatrix N := by
  classical
  ext y x
  simp only [piMatrix, Matrix.mul_apply]
  simpa only [← Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun j k => M j (y j) k * N j k (x j)))

lemma piMatrix_single {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α]
    (j : J) (U : Matrix α α ℂ) (y x : J → α) :
    piMatrix (fun k => if k = j then U else 1) y x =
      if (∀ k, k ≠ j → y k = x k) then U (y j) (x j) else 0 := by
  classical
  by_cases hm : ∀ k, k ≠ j → y k = x k
  · rw [if_pos hm]
    unfold piMatrix
    rw [Finset.prod_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj, Matrix.one_apply, hm k hkj]
    · simp
  · rw [if_neg hm]
    push Not at hm
    obtain ⟨k,hkj,hxy⟩ := hm
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hkj, Matrix.one_apply, hxy]















lemma pairMatrix_one (r : ℕ) : pairMatrix r (fun _ => 1) = 1 := by
  simp [pairMatrix,piMatrix_one]

lemma pairMatrix_mul (r : ℕ) (M N : Fin r → Matrix (Basis 2) (Basis 2) ℂ) :
    pairMatrix r (fun j => M j * N j) = pairMatrix r M * pairMatrix r N := by
  simp only [pairMatrix,piMatrix_mul]
  rw [Matrix.submatrix_mul_equiv _ _ (pairEquiv r) (pairEquiv r) (pairEquiv r)]

lemma pair_mask (r : ℕ) (j : Fin r) (y x : Basis (r*2)) :
    (∀ w, (∀ i, pairEmbedding r j i ≠ w) → y w = x w) ↔
      ∀ k, k ≠ j → pairEquiv r y k = pairEquiv r x k := by
  constructor
  · intro h k hk
    funext i
    apply h
    intro a ha
    have := (Prod.mk.inj (finProdFinEquiv.injective ha)).1
    exact hk this.symm
  · intro h w hw
    have hj : w.divNat ≠ j := by
      intro heq
      apply hw w.modNat
      subst j
      simp
    have heq := congrFun (h w.divNat hj) w.modNat
    change y (pairEmbedding r w.divNat w.modNat) = x (pairEmbedding r w.divNat w.modNat) at heq
    simpa only [pairEmbedding_divModNat] using heq

lemma pair_gate_matrix (r : ℕ) (j : Fin r) :
    (hhAt (pairEmbedding r j)).matrix =
      pairMatrix r (fun k => if k = j then hadamardTwoMatrix else 1) := by
  classical
  ext y x
  change (if (∀ w, (∀ i, pairEmbedding r j i ≠ w) → y w = x w) then
    hadamardTwoMatrix (y ∘ pairEmbedding r j) (x ∘ pairEmbedding r j) else 0) = _
  simp only [pair_mask]
  simpa [pairMatrix,pairEquiv,Function.comp_def] using
    (piMatrix_single j hadamardTwoMatrix (pairEquiv r y) (pairEquiv r x)).symm



lemma pairList_matrix {r : ℕ} (js : List (Fin r)) :
    circuitMatrix (js.map fun j => hhAt (pairEmbedding r j)) = pairMatrix r (pairProduct js) := by
  induction js with
  | nil => exact (pairMatrix_one r).symm
  | cons j js ih =>
    simp only [List.map_cons,circuitMatrix,ih,pair_gate_matrix,← pairMatrix_mul]
    congr 1
    funext k
    simp [pairProduct]

lemma pairProduct_finRange (r : ℕ) : pairProduct (List.finRange r) = fun _ => hadamardTwoMatrix := by
  classical
  funext k
  unfold pairProduct
  rw [List.prod_map_eq_pow_single k (fun j => if k = j then hadamardTwoMatrix else 1)
    (fun j hj _ => by simp [Ne.symm hj])]
  simp

lemma bank_product (r : ℕ) :
    circuitMatrix ((List.finRange r).map fun j => hhAt (pairEmbedding r j)) =
      pairMatrix r (fun _ => hadamardTwoMatrix) := by
  rw [pairList_matrix,pairProduct_finRange]






lemma hadamardTwo_factor (y x : Basis 2) :
    hadamardTwoMatrix y x = ∏ i : Fin 2, bitFactor (y i) (x i) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1/2 := by
    rw [← _root_.mul_inv_rev,hs]
    norm_num
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : x 0 <;> cases h3 : x 1 <;>
    norm_num [Fin.prod_univ_two,bitFactor,hadamardTwoMatrix,h0,h1,h2,h3,div_eq_mul_inv,hinv]

lemma hadamard_bits_product (k : ℕ) (y x : Basis k) :
    indexHadamard k (bitsEquiv k y) (bitsEquiv k x) = ∏ i : Fin k, bitFactor (y i) (x i) := by
  have hc : ((Finset.range k).filter (fun i =>
      (littleValue y).testBit i && (littleValue x).testBit i)).card =
      ∑ i : Fin k, if y i && x i then 1 else 0 := by
    have hsum : ((Finset.range k).filter (fun i =>
        (littleValue y).testBit i && (littleValue x).testBit i)).card =
        ∑ i : Fin k, if (littleValue y).testBit i && (littleValue x).testBit i then 1 else 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if (littleValue y).testBit i &&
        (littleValue x).testBit i then 1 else 0)]
      rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [hsum]
    simp_rw [littleValue_decode]
  change (-1 : ℂ) ^ ((Finset.range k).filter (fun i =>
    (littleValue y).testBit i && (littleValue x).testBit i)).card / ((Real.sqrt 2 : ℝ) : ℂ)^k = _
  rw [hc]
  simp only [bitFactor,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma pairMatrix_hadamard (r : ℕ) :
    pairMatrix r (fun _ => hadamardTwoMatrix) =
      (indexHadamard (r*2)).submatrix (bitsEquiv (r*2)) (bitsEquiv (r*2)) := by
  ext y x
  simp only [pairMatrix,Matrix.submatrix_apply,piMatrix,hadamardTwo_factor,hadamard_bits_product]
  change (∏ j : Fin r, ∏ i : Fin 2, bitFactor (y (finProdFinEquiv (j,i)))
    (x (finProdFinEquiv (j,i)))) = _
  rw [← Fintype.prod_prod_type (fun p : Fin r × Fin 2 =>
    bitFactor (y (finProdFinEquiv p)) (x (finProdFinEquiv p)))]
  exact Fintype.prod_equiv finProdFinEquiv _ _ (fun a => rfl)






lemma map_finRange_cast {a b : ℕ} {α : Type*} (h : a = b)
    (f : Fin a → α) (g : Fin b → α) (hfg : ∀ j, f j = g (Fin.cast h j)) :
    (List.finRange a).map f = (List.finRange b).map g := by
  subst b
  exact congrArg (fun f => (List.finRange a).map f) (funext hfg)

lemma pairedHadamards_lift {n : ℕ} (r : ℕ) (e : Fin (r*2) ↪ Fin n) :
    pairedHadamards e =
      (((List.finRange r).map fun j => hhAt (pairEmbedding r j)).map (Instr.mapWires e)) := by
  simp only [pairedHadamards,List.map_map]
  apply map_finRange_cast (by omega : r*2/2 = r)
  intro j
  change hhAt (pairTargets e j) = hhAt ((pairEmbedding r (Fin.cast _ j)).trans e)
  congr 1
  apply Function.Embedding.ext
  intro i
  apply congrArg e
  apply Fin.ext
  dsimp [pairTargets,pairEmbedding,finProdFinEquiv]
  omega

/-- Exact physical-bank semantics, with explicit little-endian index decoding. -/
theorem pairedHadamards_matrix {n : ℕ} (r : ℕ) (e : Fin (r*2) ↪ Fin n) :
    circuitMatrix (pairedHadamards e) =
      placeMatrix e ((indexHadamard (r*2)).submatrix (bitsEquiv (r*2)) (bitsEquiv (r*2))) := by
  rw [pairedHadamards_lift,circuitMatrix_mapWires,bank_product,pairMatrix_hadamard]


/-- Even-width registers are exhausted by the paired G₂ bank. -/
theorem pairedHadamards_matrix_even {k n : ℕ} (e : Fin k ↪ Fin n) (hk : Even k) :
    circuitMatrix (pairedHadamards e) =
      placeMatrix e ((indexHadamard k).submatrix (bitsEquiv k) (bitsEquiv k)) := by
  obtain ⟨r,hr⟩ := hk
  have heq : k = r*2 := by omega
  clear hr
  subst k
  exact pairedHadamards_matrix r e






lemma indexQubits_even (V : Verifier gatesG2) : Even (indexQubits V) := by
  rw [Nat.even_iff]
  dsimp only [indexQubits]
  omega

end QMAPerfectCompleteness.Main.IndexHadamards

end

/- Inline helpers retained from Solutions.BlockImplements. -/
section


/-! Exact realization of the literal paper compiler on the published wire layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements
open BlockCompiler BlockCoordinates BlockClockCoordinates ReversibleGadgets







lemma mul_basisEmbedding {α β : Type*} [Fintype α] [Fintype β] (e : α → β)
    (C : Matrix β β ℂ) (y : β) (x : α) : (C*basisEmbedding e) y x = C y (e x) := by
  classical
  simp [Matrix.mul_apply,basisEmbedding,mul_ite]







variable (V : Verifier gatesG2)






































end QMAPerfectCompleteness.Main.BlockImplements

end

/- Inline helpers retained from Solutions.BlockHadamardCoordinates. -/
section


/-! The physical paired-H bank implements the logical H bank with clean workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
open BlockCircuit BlockCoordinates BlockCompiler



lemma spectator_coordinates (V : Verifier gatesG2) (w : ℕ)
    (y x : Basis (bodyWires V+w)) :
    (∀ j, (∀ a, (indexWire (V := V) (w := w) a) ≠ j) → y j = x j) ↔
      (coordinates V w y).1.2 = (coordinates V w x).1.2 ∧
        (coordinates V w y).2 = (coordinates V w x).2 := by
  rw [spectator_mask]
  change _ ↔ (clockEquiv V (y ∘ clockWire),y ∘ verifierWire,y flagWire) =
      (clockEquiv V (x ∘ clockWire),x ∘ verifierWire,x flagWire) ∧
      (y ∘ workspaceWire = x ∘ workspaceWire)
  simp only [Prod.ext_iff,Equiv.apply_eq_iff_eq]
  tauto







end QMAPerfectCompleteness.Main.BlockHadamardCoordinates

end

/- Inline helpers retained from Solutions.CoordinateFibers. -/
section


/-! Matrix transport on a workspace fiber determined by conserved classical coordinates. -/
open Matrix
namespace QMAPerfectCompleteness.Main.CoordinateFibers

variable {P A K W : Type*} [Fintype A] [DecidableEq P] [DecidableEq W]

/-- Workspace computed from a conserved key may remain present during a quantum operation.
The conclusion is the exact matrix-column intertwining equation used in coherent circuits. -/
theorem column (coords : P ≃ A × W) (key : A → K)
    (U : Matrix A A ℂ) (C : Matrix P P ℂ)
    (hC : ∀ y x, C y x = U (coords y).1 (coords x).1 *
      (if (coords y).2 = (coords x).2 then 1 else 0))
    (hu : ∀ a b, key a ≠ key b → U a b = 0)
    (e : A → P) (s : K → W) (he : ∀ a, coords (e a) = (a,s (key a)))
    (y : P) (a : A) :
    C y (e a) = ∑ b, (if y=e b then (1 : ℂ) else 0) * U b a := by
  classical
  have hd (b : A) : (coords (e b)).1 = b := congrArg Prod.fst (he b)
  have hsum : (∑ b, (if y=e b then (1 : ℂ) else 0)*U b a) =
      if y=e (coords y).1 then U (coords y).1 a else 0 := by
    rw [Finset.sum_eq_single (coords y).1]
    · split_ifs <;> simp
    · intro b _ hb
      have hy : y ≠ e b := by intro hy; exact hb ((congrArg (fun z => (coords z).1) hy).trans (hd b)).symm
      simp [hy]
    · simp
  rw [hsum,hC,he]
  have hy : y=e (coords y).1 ↔ (coords y).2=s (key (coords y).1) := by
    rw [← coords.apply_eq_iff_eq,he,Prod.ext_iff]
    simp
  simp only [hy]
  by_cases hk : key (coords y).1 = key a
  · simp only [hk]
    split_ifs <;> simp
  · rw [hu _ _ hk]
    simp

end QMAPerfectCompleteness.Main.CoordinateFibers

end

/- Inline helpers retained from Solutions.CertificateVerifierCoordinates. -/
section


/-! Lift the two quantum calls through retained certificate and workspace coordinates. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateVerifierCoordinates
open BlockCircuit BlockCoordinates CertificateCoordinates BlockVerifierCoordinates ReversibleGadgets



lemma prefix_mask (n q : ℕ) (y x : Basis (n+q)) :
    (∀ j, (∀ a, prefixEmbedding n q a ≠ j) → y j=x j) ↔
      (splitBasis n q y).2 = (splitBasis n q x).2 := by
  constructor
  · intro h
    funext j
    apply h
    intro a ha
    have hv := congrArg Fin.val ha
    have ha' := a.isLt
    change a.val=n+j.val at hv
    omega
  · intro h j
    refine Fin.addCases (m := n) (n := q) (fun a => ?_) (fun a => ?_) j
    · intro hj; exact (hj a rfl).elim
    · intro _; exact congrFun h a

lemma placePrefix (n q : ℕ) (A : Matrix (Basis n) (Basis n) ℂ) :
    placeMatrix (prefixEmbedding n q) A =
      (A ⊗ₖ (1 : Matrix (Basis q) (Basis q) ℂ)).submatrix (splitBasis n q) (splitBasis n q) := by
  ext y x
  rw [placeMatrix_apply]
  simp only [prefix_mask]
  simp only [Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
  split_ifs <;> simp <;> rfl

/-- Reordering (body,work),certificate to (body,certificate),work preserves the tensor operator. -/
lemma prefix_coordinates (V : Verifier gatesG2) (w : ℕ)
    (A : Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ) :
    placeMatrix (prefixEmbedding (bodyWires V+w) (claimQubits V))
      ((A ⊗ₖ (1 : Matrix (Basis w) (Basis w) ℂ)).submatrix (coordinates V w) (coordinates V w)) =
      (((A ⊗ₖ (1 : Matrix (CertificateMixture.Claim V) (CertificateMixture.Claim V) ℂ)) ⊗ₖ
        (1 : Matrix (Basis w) (Basis w) ℂ))).submatrix
        (computationEquiv V w) (computationEquiv V w) := by
  rw [placePrefix]
  ext y x
  simp only [Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
  change (A (coordinates V w (splitBasis _ _ y).1).1 (coordinates V w (splitBasis _ _ x).1).1 *
    (if (coordinates V w (splitBasis _ _ y).1).2 = (coordinates V w (splitBasis _ _ x).1).2 then 1 else 0)) *
      (if (splitBasis _ _ y).2 = (splitBasis _ _ x).2 then 1 else 0) =
    (A (coordinates V w (splitBasis _ _ y).1).1 (coordinates V w (splitBasis _ _ x).1).1 *
      (if claimEquiv V (splitBasis _ _ y).2 = claimEquiv V (splitBasis _ _ x).2 then 1 else 0)) *
        (if (coordinates V w (splitBasis _ _ y).1).2 = (coordinates V w (splitBasis _ _ x).1).2 then 1 else 0)
  simp only [Equiv.apply_eq_iff_eq]
  ring




















end QMAPerfectCompleteness.Main.CertificateVerifierCoordinates

end

/- Inline helpers retained from Solutions.CertificateHadamardCoordinates. -/
section


/-! The index Hadamards preserve certificate-dependent arithmetic workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateHadamardCoordinates
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateVerifierCoordinates ReversibleGadgets



lemma placeIndex_coordinates (V : Verifier gatesG2) (w : ℕ)
    (H : Matrix (Fin (2^indexQubits V)) (Fin (2^indexQubits V)) ℂ) :
    placeMatrix (indexEmbedding V w)
      (H.submatrix (IndexHadamards.bitsEquiv _) (IndexHadamards.bitsEquiv _)) =
      ((H ⊗ₖ (1 : Matrix V.Body V.Body ℂ)) ⊗ₖ
        (1 : Matrix (Basis w) (Basis w) ℂ)).submatrix (coordinates V w) (coordinates V w) := by
  ext y x
  rw [placeMatrix_apply]
  change (if ∀ j, (∀ a, (indexWire (V := V) a) ≠ j) → y j = x j then
    H (IndexHadamards.bitsEquiv _ (y ∘ indexWire))
      (IndexHadamards.bitsEquiv _ (x ∘ indexWire)) else 0) = _
  simp only [BlockHadamardCoordinates.spectator_coordinates,Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply,Matrix.one_apply]
  change (if (coordinates V w y).1.2 = (coordinates V w x).1.2 ∧
    (coordinates V w y).2 = (coordinates V w x).2 then
      H (coordinates V w y).1.1 (coordinates V w x).1.1 else 0) = _
  by_cases hb : (coordinates V w y).1.2 = (coordinates V w x).1.2
  · by_cases hw : (coordinates V w y).2 = (coordinates V w x).2
    · simp only [hb,hw,if_true,and_self,mul_one]
    · simp only [hb,hw,if_false,and_false,mul_zero]
  · simp only [hb,if_false,false_and,mul_zero,zero_mul]





theorem physicalH_coordinates (V : Verifier gatesG2) (w : ℕ)
    (H : Matrix (Fin (2^indexQubits V)) (Fin (2^indexQubits V)) ℂ) :
    physicalH V w H =
      (logicalH V H ⊗ₖ (1 : Matrix (Basis w) (Basis w) ℂ)).submatrix
        (computationEquiv V w) (computationEquiv V w) := by
  rw [physicalH,placeIndex_coordinates,prefix_coordinates]
  rfl

/-- The same H layer can be applied before and after SELECT even while threshold words remain
computed: those words depend on the retained certificate, which the H layer never changes. -/
theorem hadamard_fiber (V : Verifier gatesG2) (w : ℕ)
    (H : Matrix (Fin (2^indexQubits V)) (Fin (2^indexQubits V)) ℂ)
    (e : CoherentCertificate.ComputationReg V → Basis ((bodyWires V+w)+claimQubits V))
    (s : CertificateMixture.Claim V → Basis w)
    (he : ∀ p, computationEquiv V w (e p) = (p,s p.2))
    (y : Basis ((bodyWires V+w)+claimQubits V)) (p : CoherentCertificate.ComputationReg V) :
    physicalH V w H y (e p) =
      ∑ q, (if y=e q then (1 : ℂ) else 0) * logicalH V H q p := by
  apply CoordinateFibers.column (computationEquiv V w) Prod.snd (logicalH V H) (physicalH V w H)
  · intro y x
    rw [physicalH_coordinates]
    rfl
  · intro a b h
    simp [logicalH,Matrix.kroneckerMap_apply,Matrix.one_apply,h]
  · exact he



theorem gates_matrix (V : Verifier gatesG2) (w : ℕ) :
    circuitMatrix (gates V w) = physicalH V w (indexHadamard (indexQubits V)) := by
  rw [gates,circuitMatrix_mapWires,
    IndexHadamards.pairedHadamards_matrix_even _ (IndexHadamards.indexQubits_even V)]
  rfl

end QMAPerfectCompleteness.Main.CertificateHadamardCoordinates

end

/- Inline helpers retained from Solutions.CertificateBlockCorrectness. -/
section


/-! Exact coherent block SELECT on the master certificate register layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout CertificateCoordinates BlockCoordinates BlockCompiler
open ReversibleGadgets BlockImplements
variable (V : Verifier gatesG2)










@[simp] lemma coords_embed (s : Key V → Basis (work V)) (p : Logical V) :
    coords V (embed V s p) = (p,s (key V p)) := (coords V).apply_symm_apply _



















































end QMAPerfectCompleteness.Main.CertificateBlockCorrectness

end



/-! Quantum calls and both H banks on the prepared arithmetic workspace fibers. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
end QMAPerfectCompleteness.Main.CertificateBlockCorrectness
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout BlockImplements
variable (V : Verifier gatesG2)









theorem solution (s : CertificateMixture.Claim V → Basis (work V)) :
    Transports (embed V (certSpace V s)) (embed V (certSpace V s))
      (circuitMatrix (CertificateHadamardCoordinates.gates V (work V)))
      (CertificateHadamardCoordinates.logicalH V (indexHadamard (indexQubits V))) := by
  ext y p
  rw [mul_basisEmbedding,CertificateHadamardCoordinates.gates_matrix,Matrix.mul_apply,
    CertificateHadamardCoordinates.hadamard_fiber V (work V) (indexHadamard (indexQubits V))
      (embed V (certSpace V s)) s (coords_embed V (certSpace V s)) y p]
  apply Finset.sum_congr rfl
  intro q _
  by_cases he : y=embed V (certSpace V s) q <;> simp [basisEmbedding,he]

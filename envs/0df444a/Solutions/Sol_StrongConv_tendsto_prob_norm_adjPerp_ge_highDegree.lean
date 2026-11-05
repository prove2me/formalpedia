-- Prove2me | solution 1 for StrongConv.tendsto_prob_norm_adjPerp_ge_highDegree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:05:13.071111+00:00
-- url     : https://prove2.me/submissions/a12e45a0-fde8-427e-9248-ed1d2f00b410

import Mathlib
import Definitions.Def_StrongConv

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
/-!
# Blueprint: the high-degree lower bound ‖Aᴺ‖ ≥ (1 − δ)·2√(2d − 1) (Brailovskaya–van Handel, Remark 3.9)

Fixed-`p` second-moment trace method.

* `T(σ) = ∑_w (fix σ_w − 1)` over all words `w` of length `2p` in the `2d` letters satisfies
  `T(σ) ≤ (N − 1)‖Aᴺ‖^{2p}` (Part LA).
* Words reducing to `1` contribute `N − 1` each; there are at least `Cat_p·2^p·(d − p)^p` of them
  (Part K).
* Words in which some generator occurs exactly once have `E[fix σ_w] = 1` (Part E); those with no
  such generator are few (`≤ (2p)^{2p} d^p`, Part W) and contribute `≥ −1` each.
* The once-letter part `R₁` has `E[R₁²] = O(d^{2p} + N² d^{2p−1})` (Part S), so Chebyshev makes
  `R₁ ≥ −(N − 1)K/4` with probability `→ 1`.
-/
/-! ## Words -/
/-- A letter: generator `i`, inverted iff the flag is `true`. -/
abbrev Ltr (d : ℕ) := Fin d × Bool

/-- A letter as an element of the free group. -/
def ltrFG {d : ℕ} (l : Ltr d) : FreeGroup (Fin d) :=
  if l.2 then (FreeGroup.of l.1)⁻¹ else FreeGroup.of l.1

/-- A word of length `n` as an element of the free group (product in order). -/
def wordFG {d n : ℕ} (w : Fin n → Ltr d) : FreeGroup (Fin d) :=
  (List.ofFn fun j => ltrFG (w j)).prod

/-- The permutation a word stands for. -/
def wordPerm {d N n : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : Fin n → Ltr d) :
    Equiv.Perm (Fin N) :=
  FreeGroup.lift σ (wordFG w)

/-- Number of fixed points of a permutation. -/
def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card

/-- `fix σ_w` as a real number. -/
def fixW {d N n : ℕ} (w : Fin n → Ltr d) (σ : Fin d → Equiv.Perm (Fin N)) : ℝ :=
  (fixCount (wordPerm σ w) : ℝ)

/-- Number of occurrences of generator `i` in `w` (either orientation). -/
def genCount {d n : ℕ} (w : Fin n → Ltr d) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun j => (w j).1 = i).card

/-- Some generator occurs exactly once in `w`. -/
def HasOnce {d n : ℕ} (w : Fin n → Ltr d) : Prop :=
  ∃ i, genCount w i = 1

/-- The set of generators occurring in `w`. -/
def gens {d n : ℕ} (w : Fin n → Ltr d) : Finset (Fin d) :=
  Finset.univ.image fun j => (w j).1

/-- Number of words of length `n` reducing to `1`. -/
def retCount (d n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Ltr d => wordFG w = 1).card

/-- `T(σ) = ∑_w (fix σ_w − 1)` over words of length `n`. -/
def trMoment {d N : ℕ} (n : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) : ℝ :=
  ∑ w : Fin n → Ltr d, (fixW w σ - 1)

/-- The once-letter part `R₁(σ) = ∑_{w has a once-generator} (fix σ_w − 1)`. -/
def onceSum {d N : ℕ} (n : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) : ℝ := by
  classical exact ∑ w ∈ Finset.univ.filter (fun w : Fin n → Ltr d => HasOnce w), (fixW w σ - 1)

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartLA
open scoped InnerProductSpace
lemma permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

lemma permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

lemma permOpPerp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    (permOpPerp π x : EuclideanSpace ℂ (Fin N)) = permOp π x := rfl

lemma permOpPerp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOpPerp (π * ρ) = permOpPerp π * permOpPerp ρ := by
  ext x : 2
  simp [permOpPerp_apply, permOp_mul]

lemma permOpPerp_one {N : ℕ} : permOpPerp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x : 2
  simp [permOpPerp_apply, permOp_one]

lemma inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪permOp π x, y⟫_ℂ = ⟪x, permOp π⁻¹ y⟫_ℂ := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

lemma star_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    star (permOpPerp π) = permOpPerp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, permOpPerp_apply]
  rw [inner_permOp, inv_inv]

lemma trace_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) = (fixCount π : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    ContinuousLinearMap.coe_coe, permOp_apply]
  rw [fixCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (π.symm i = i) ↔ (π i = i) := by
    rw [Equiv.symm_apply_eq, eq_comm]
  by_cases h : π i = i
  · simp [h, this.mpr h]
  · simp [h, mt this.mp h]

lemma trace_eq_add_of_isCompl {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (p q : Submodule ℂ M) (h : IsCompl p q) (f : M →ₗ[ℂ] M)
    (hp : Set.MapsTo f p p) (hq : Set.MapsTo f q q) :
    LinearMap.trace ℂ M f = LinearMap.trace ℂ p (f.restrict hp) +
      LinearMap.trace ℂ q (f.restrict hq) := by
  let A : Fin 2 → Submodule ℂ M := ![p, q]
  have hA : DirectSum.IsInternal A :=
    (DirectSum.isInternal_submodule_iff_isCompl A (i := 0) (j := 1) (by decide)
      (by ext k; fin_cases k <;> simp)).mpr h
  have hf : ∀ i, Set.MapsTo f (A i) (A i) := by
    intro i; fin_cases i
    · exact hp
    · exact hq
  rw [LinearMap.trace_eq_sum_trace_restrict hA hf, Fin.sum_univ_two]
  rfl

lemma onesVec_ne_zero {N : ℕ} (hN : 1 ≤ N) : onesVec N ≠ 0 := by
  intro h0
  have := congr_arg (fun v : EuclideanSpace ℂ (Fin N) => v ⟨0, hN⟩) h0
  simp [onesVec] at this

lemma trace_permOpPerp {N : ℕ} (hN : 1 ≤ N) (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) = (fixCount π : ℂ) - 1 := by
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin N)) := ℂ ∙ onesVec N with hK
  have hones : permOp π (onesVec N) = onesVec N := by
    ext j; simp [permOp_apply, onesVec]
  have hp : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) K K := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [ContinuousLinearMap.coe_coe, map_smul, hones]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hq : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) Kᗮ Kᗮ := by
    intro x hx
    exact (permOpPerp π ⟨x, hx⟩).2
  have h := trace_eq_add_of_isCompl K Kᗮ (Submodule.isCompl_orthogonal K)
    _ hp hq
  rw [trace_permOp] at h
  have h1 : LinearMap.restrict _ hp = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    show permOp π (c • onesVec N) = c • onesVec N
    rw [map_smul, hones]
  have h2 : LinearMap.restrict _ hq = ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) := by
    ext x; rfl
  have hr : Module.finrank ℂ K = 1 := finrank_span_singleton (onesVec_ne_zero hN)
  rw [h1, h2, LinearMap.trace_id, hr] at h
  rw [h]
  push_cast
  ring

lemma finrank_onesPerp {N : ℕ} (hN : 1 ≤ N) : Module.finrank ℂ (OnesPerp N) = N - 1 := by
  apply Submodule.finrank_add_finrank_orthogonal'
  rw [finrank_span_singleton (onesVec_ne_zero hN), finrank_euclideanSpace, Fintype.card_fin]
  omega

/-- The operator of a letter. -/
def ltrOp {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (l : Ltr d) : OnesPerp N →L[ℂ] OnesPerp N :=
  permOpPerp (FreeGroup.lift σ (ltrFG l))

lemma adjPerp_eq_sum {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    adjPerp σ = ∑ l : Ltr d, ltrOp σ l := by
  rw [adjPerp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp [ltrOp, ltrFG, sModel, star_permOpPerp, add_comm]

lemma wordFG_cons {d n : ℕ} (l : Ltr d) (w : Fin n → Ltr d) :
    wordFG (Fin.cons l w : Fin (n + 1) → Ltr d) = ltrFG l * wordFG w := by
  simp [wordFG, List.ofFn_succ]

lemma sum_cons {X M : Type*} [Fintype X] [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → X) → M) :
    ∑ w, f w = ∑ l : X, ∑ w : Fin n → X, f (Fin.cons l w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => X) _ _ (fun _ => rfl)).symm

lemma adjPerp_pow {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (n : ℕ) :
    adjPerp σ ^ n = ∑ w : Fin n → Ltr d, permOpPerp (wordPerm σ w) := by
  induction n with
  | zero => simp [wordPerm, wordFG, permOpPerp_one]
  | succ n ih =>
    rw [pow_succ', ih, adjPerp_eq_sum, sum_cons, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [wordPerm]
    rw [wordFG_cons, map_mul, permOpPerp_mul]
    rfl

lemma inner_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : OnesPerp N) :
    ⟪permOpPerp π x, y⟫_ℂ = ⟪x, permOpPerp π⁻¹ y⟫_ℂ := by
  simp only [Submodule.coe_inner, permOpPerp_apply]
  exact inner_permOp _ _ _

lemma ltrFG_flip {d : ℕ} (l : Ltr d) : ltrFG ((l.1, !l.2) : Ltr d) = (ltrFG l)⁻¹ := by
  rcases l with ⟨i, _ | _⟩ <;> simp [ltrFG]

lemma inner_adjPerp {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x y : OnesPerp N) :
    ⟪adjPerp σ x, y⟫_ℂ = ⟪x, adjPerp σ y⟫_ℂ := by
  rw [adjPerp_eq_sum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, sum_inner,
    inner_sum]
  let e : Ltr d ≃ Ltr d := Function.Involutive.toPerm (fun l => ((l.1, !l.2) : Ltr d))
    (by intro l; simp)
  refine Fintype.sum_equiv e _ _ fun l => ?_
  have he : e l = ((l.1, !l.2) : Ltr d) := rfl
  rw [he, ltrOp, ltrOp, inner_permOpPerp, ltrFG_flip, map_inv]

lemma inner_adjPerp_pow {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (p : ℕ) (x y : OnesPerp N) :
    ⟪(adjPerp σ ^ p) x, y⟫_ℂ = ⟪x, (adjPerp σ ^ p) y⟫_ℂ := by
  induction p generalizing x y with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', mul_apply_eq_comp, inner_adjPerp, ih, ← mul_apply_eq_comp, ← pow_succ,
      pow_succ']

lemma norm_pow_apply_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (x : E) (p : ℕ) : ‖(A ^ p) x‖ ≤ ‖A‖ ^ p * ‖x‖ := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_assoc]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

theorem trMoment_le {d N : ℕ} (hN : 1 ≤ N) (σ : Fin d → Equiv.Perm (Fin N)) (p : ℕ) :
    trMoment (2 * p) σ ≤ ((N : ℝ) - 1) * ‖adjPerp σ‖ ^ (2 * p) := by
  set A := adjPerp σ
  set b := stdOrthonormalBasis ℂ (OnesPerp N)
  -- the trace of `A^{2p}` is `trMoment`
  have htr : (LinearMap.trace ℂ _ ((A ^ (2 * p) : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N)) = (trMoment (2 * p) σ : ℂ) := by
    rw [adjPerp_pow, ContinuousLinearMap.toLinearMap_sum, map_sum, trMoment]
    push_cast
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [trace_permOpPerp hN, fixW]
    simp
  have hterm : ∀ k, ⟪b k, (A ^ (2 * p)) (b k)⟫_ℂ = ((‖(A ^ p) (b k)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [two_mul, pow_add, mul_apply_eq_comp]
    rw [← inner_adjPerp_pow σ p, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  rw [LinearMap.trace_eq_sum_inner _ b] at htr
  simp only [ContinuousLinearMap.coe_coe, hterm] at htr
  have hreal : trMoment (2 * p) σ = ∑ k, ‖(A ^ p) (b k)‖ ^ 2 := by
    exact_mod_cast htr.symm
  rw [hreal]
  calc ∑ k, ‖(A ^ p) (b k)‖ ^ 2 ≤ ∑ _k : Fin (Module.finrank ℂ (OnesPerp N)), ‖A‖ ^ (2 * p) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 := norm_pow_apply_le A (b k) p
        rw [b.orthonormal.1 k, mul_one] at h1
        calc ‖(A ^ p) (b k)‖ ^ 2 ≤ (‖A‖ ^ p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = ‖A‖ ^ (2 * p) := by ring
    _ = ((N : ℝ) - 1) * ‖A‖ ^ (2 * p) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_onesPerp hN,
          nsmul_eq_mul]
        congr 1
        rw [Nat.cast_sub hN]; simp

end PartLA
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
/-! ## Part LA: the trace inequality -/
alias trMoment_le := StrongConv.HighDeg.PartLA.trMoment_le

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartK
/-- The inverse letter. -/
def flipL {d : ℕ} (x : Ltr d) : Ltr d := (x.1, !x.2)

lemma ltrFG_flipL {d : ℕ} (x : Ltr d) : ltrFG (flipL x) = (ltrFG x)⁻¹ := by
  rcases x with ⟨i, _ | _⟩ <;> simp [ltrFG, flipL]

/-- The word of a binary tree whose nodes (in preorder) carry the letters of `L`:
`enc (node l r) (x :: L) = x · enc l · x⁻¹ · enc r`. -/
def enc {d : ℕ} : BinaryTree Unit → List (Ltr d) → List (Ltr d)
  | .nil, _ => []
  | .node _ _ _, [] => []
  | .node _ l r, x :: L => x :: (enc l (L.take l.numNodes) ++ flipL x :: enc r (L.drop l.numNodes))

lemma length_enc {d : ℕ} (t : BinaryTree Unit) (L : List (Ltr d)) (h : L.length = t.numNodes) :
    (enc t L).length = 2 * t.numNodes := by
  induction t generalizing L with
  | nil => simp [enc]
  | node _ l r hl hr =>
    rcases L with _ | ⟨x, L⟩
    · simp at h
    · simp only [BinaryTree.numNodes, List.length_cons] at h
      simp only [enc, List.length_cons, List.length_append]
      rw [hl _ (by simp; omega), hr _ (by simp; omega), BinaryTree.numNodes]
      ring

lemma prod_enc {d : ℕ} (t : BinaryTree Unit) (L : List (Ltr d)) :
    ((enc t L).map ltrFG).prod = 1 := by
  induction t generalizing L with
  | nil => simp [enc]
  | node _ l r hl hr =>
    rcases L with _ | ⟨x, L⟩
    · simp [enc]
    · simp only [enc, List.map_cons, List.map_append, List.prod_cons, List.prod_append, hl, hr,
        ltrFG_flipL]
      group

lemma fst_mem_of_mem_enc {d : ℕ} (t : BinaryTree Unit) (L : List (Ltr d)) :
    ∀ y ∈ enc t L, y.1 ∈ L.map Prod.fst := by
  induction t generalizing L with
  | nil => simp [enc]
  | node _ l r hl hr =>
    rcases L with _ | ⟨x, L⟩
    · simp [enc]
    · intro y hy
      simp only [enc, List.mem_cons, List.mem_append] at hy
      rcases hy with rfl | hy | rfl | hy
      · simp
      · have := hl _ y hy
        exact List.mem_cons_of_mem _ (List.map_subset _ (List.take_subset _ _) this)
      · simp [flipL]
      · have := hr _ y hy
        exact List.mem_cons_of_mem _ (List.map_subset _ (List.drop_subset _ _) this)

lemma flipL_not_mem {d : ℕ} (t : BinaryTree Unit) (x : Ltr d) (M L : List (Ltr d))
    (hsub : M.Sublist L) (hx : x.1 ∉ L.map Prod.fst) : flipL x ∉ enc t M := by
  intro h
  exact hx (List.map_subset _ hsub.subset (fst_mem_of_mem_enc t M (flipL x) h))

lemma enc_inj {d : ℕ} (t : BinaryTree Unit) :
    ∀ (t' : BinaryTree Unit) (L L' : List (Ltr d)), L.length = t.numNodes →
      L'.length = t'.numNodes → (L.map Prod.fst).Nodup → (L'.map Prod.fst).Nodup →
      enc t L = enc t' L' → t = t' ∧ L = L' := by
  induction t with
  | nil =>
    intro t' L L' hL hL' _ _ he
    rcases t' with _ | ⟨_, l', r'⟩
    · simp only [BinaryTree.numNodes, List.length_eq_zero_iff] at hL hL'
      exact ⟨rfl, by rw [hL, hL']⟩
    · rcases L' with _ | ⟨x', L'⟩
      · simp at hL'
      · simp [enc] at he
  | node u l r hl hr =>
    intro t' L L' hL hL' hn hn' he
    rcases L with _ | ⟨x, M⟩
    · simp at hL
    rcases t' with _ | ⟨u', l', r'⟩
    · simp [enc] at he
    rcases L' with _ | ⟨x', M'⟩
    · simp at hL'
    simp only [BinaryTree.numNodes, List.length_cons] at hL hL'
    simp only [enc, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    have hx : x.1 ∉ M.map Prod.fst := (List.nodup_cons.mp (by simpa using hn)).1
    have hx' : x.1 ∉ M'.map Prod.fst := (List.nodup_cons.mp (by simpa using hn')).1
    have hM : (M.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hn)).2
    have hM' : (M'.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hn')).2
    rw [List.append_cons_inj_of_notMem (flipL_not_mem _ _ _ _ (List.take_sublist _ _) hx)
      (flipL_not_mem _ _ _ _ (List.drop_sublist _ _) hx)] at he
    obtain ⟨h1, -, h2⟩ := he
    obtain ⟨rfl, h1'⟩ := hl l' _ _ (by simp; omega) (by simp; omega)
      (hM.sublist ((List.take_sublist _ _).map _))
      (hM'.sublist ((List.take_sublist _ _).map _)) h1
    obtain ⟨rfl, h2'⟩ := hr r' _ _ (by simp; omega) (by simp; omega)
      (hM.sublist ((List.drop_sublist _ _).map _))
      (hM'.sublist ((List.drop_sublist _ _).map _)) h2
    refine ⟨rfl, ?_⟩
    rw [← List.take_append_drop l.numNodes M, ← List.take_append_drop l.numNodes M', h1', h2']

/-- A list of length `n` as a function on `Fin n`. -/
def toFn {α : Type*} {n : ℕ} (E : List α) (h : E.length = n) : Fin n → α :=
  fun j => E[(j : ℕ)]'(by rw [h]; exact j.2)

lemma ofFn_toFn {α : Type*} {n : ℕ} (E : List α) (h : E.length = n) :
    List.ofFn (toFn E h) = E := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [toFn]

/-- The letters attached to the nodes. -/
def lettersOf {d p : ℕ} (f : Fin p ↪ Fin d) (b : Fin p → Bool) : List (Ltr d) :=
  List.ofFn fun k => ((f k, b k) : Ltr d)

lemma lettersOf_length {d p : ℕ} (f : Fin p ↪ Fin d) (b : Fin p → Bool) :
    (lettersOf f b).length = p := by simp [lettersOf]

lemma lettersOf_nodup {d p : ℕ} (f : Fin p ↪ Fin d) (b : Fin p → Bool) :
    ((lettersOf f b).map Prod.fst).Nodup := by
  rw [lettersOf, List.map_ofFn]
  exact List.nodup_ofFn.mpr f.injective

lemma enc_length' {d p : ℕ} (t : {t : BinaryTree Unit // t ∈ BinaryTree.treesOfNumNodesEq p})
    (f : Fin p ↪ Fin d) (b : Fin p → Bool) : (enc t.1 (lettersOf f b)).length = 2 * p := by
  have ht := BinaryTree.mem_treesOfNumNodesEq.mp t.2
  rw [length_enc _ _ (by rw [lettersOf_length, ht]), ht]

/-- The word attached to a tree, distinct generators and orientations. -/
def wordOf {d p : ℕ}
    (x : {t : BinaryTree Unit // t ∈ BinaryTree.treesOfNumNodesEq p} × (Fin p ↪ Fin d) ×
      (Fin p → Bool)) : {w : Fin (2 * p) → Ltr d // wordFG w = 1} :=
  ⟨toFn (enc x.1.1 (lettersOf x.2.1 x.2.2)) (enc_length' x.1 x.2.1 x.2.2), by
    rw [wordFG]
    have : (List.ofFn fun j => ltrFG (toFn (enc x.1.1 (lettersOf x.2.1 x.2.2))
        (enc_length' x.1 x.2.1 x.2.2) j)) =
        (List.ofFn (toFn (enc x.1.1 (lettersOf x.2.1 x.2.2))
          (enc_length' x.1 x.2.1 x.2.2))).map ltrFG := by
      rw [List.map_ofFn]; rfl
    rw [this, ofFn_toFn]
    exact prod_enc _ _⟩

lemma wordOf_injective {d p : ℕ} : Function.Injective (wordOf (d := d) (p := p)) := by
  rintro ⟨t, f, b⟩ ⟨t', f', b'⟩ h
  have h1 := congr_arg (fun w => List.ofFn w.1) h
  simp only [wordOf, ofFn_toFn] at h1
  have ht := BinaryTree.mem_treesOfNumNodesEq.mp t.2
  have ht' := BinaryTree.mem_treesOfNumNodesEq.mp t'.2
  obtain ⟨h2, h3⟩ := enc_inj t.1 t'.1 _ _ (by rw [lettersOf_length, ht])
    (by rw [lettersOf_length, ht']) (lettersOf_nodup f b) (lettersOf_nodup f' b') h1
  have h4 := List.ofFn_injective h3
  have hf : f = f' := by
    apply Function.Embedding.ext; intro k; exact congr_arg (fun g => (g k).1) h4
  have hb : b = b' := by
    funext k; exact congr_arg (fun g => (g k).2) h4
  rw [Subtype.ext h2, hf, hb]

theorem retCount_ge (d p : ℕ) (hp : p ≤ d) :
    (catalan p : ℝ) * 2 ^ p * ((d : ℝ) - p) ^ p ≤ retCount d (2 * p) := by
  classical
  have hcard := Fintype.card_le_of_injective _ (wordOf_injective (d := d) (p := p))
  rw [Fintype.card_subtype, Fintype.card_prod, Fintype.card_prod, Fintype.card_coe,
    BinaryTree.treesOfNumNodesEq_card_eq_catalan, Fintype.card_embedding_eq, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_bool] at hcard
  have hdesc : (d - p) ^ p ≤ d.descFactorial p :=
    (Nat.pow_le_pow_left (by omega) p).trans (Nat.pow_sub_le_descFactorial d p)
  have key : catalan p * 2 ^ p * (d - p) ^ p ≤ retCount d (2 * p) := by
    calc catalan p * 2 ^ p * (d - p) ^ p ≤ catalan p * (d.descFactorial p * 2 ^ p) := by
          rw [mul_assoc, mul_comm (2 ^ p)]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hdesc)
      _ ≤ retCount d (2 * p) := by
          convert hcard using 1
          rw [retCount]
  have := (Nat.cast_le (α := ℝ)).mpr key
  push_cast [Nat.cast_sub hp] at this
  exact this

end PartK
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
/-! ## Part K: words reducing to 1 -/
alias retCount_ge := StrongConv.HighDeg.PartK.retCount_ge

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartS
theorem sum_genCount {d n : ℕ} (w : Fin n → Ltr d) :
    ∑ i ∈ gens w, genCount w i = n := by
  classical
  unfold genCount
  rw [← Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (t := gens w) (f := fun j => (w j).1)]
  · simp
  · intro j _
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)

theorem card_gens_le (d n m : ℕ) (hd : 1 ≤ d) :
    ((Finset.univ.filter fun w : Fin n → Ltr d => (gens w).card ≤ m).card : ℝ) ≤
      (2 * m : ℝ) ^ n * (d : ℝ) ^ m := by
  classical
  let g : (Fin m → Fin d) × (Fin n → Fin m × Bool) → (Fin n → Ltr d) :=
    fun fc j => (fc.1 (fc.2 j).1, (fc.2 j).2)
  have hsub : (Finset.univ.filter fun w : Fin n → Ltr d => (gens w).card ≤ m) ⊆
      Finset.univ.image g := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    set s := gens w with hs
    let e := s.orderIsoOfFin rfl
    let f : Fin m → Fin d := fun a =>
      if h : a.val < s.card then (e ⟨a, h⟩ : Fin d) else ⟨0, hd⟩
    have hf : ∀ x ∈ s, ∃ a, f a = x := by
      intro x hx
      refine ⟨Fin.castLE hw (e.symm ⟨x, hx⟩), ?_⟩
      simp only [f, Fin.val_castLE, Fin.is_lt, dite_true]
      simp
    have hmem : ∀ j, (w j).1 ∈ s := fun j =>
      Finset.mem_image_of_mem _ (Finset.mem_univ j)
    refine ⟨(f, fun j => ((hf _ (hmem j)).choose, (w j).2)), ?_⟩
    funext j
    simp only [g]
    rw [(hf _ (hmem j)).choose_spec]
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_univ] at hcard
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcard
  calc ((Finset.univ.filter fun w : Fin n → Ltr d => (gens w).card ≤ m).card : ℝ)
      ≤ ((d ^ m * (m * 2) ^ n : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (2 * m : ℝ) ^ n * (d : ℝ) ^ m := by push_cast; ring

end PartS
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
/-! ## Part W: counting words by their generators -/

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartS
theorem card_gens_le_half {d n : ℕ} (w : Fin n → Ltr d)
    (h : ∀ i ∈ gens w, 2 ≤ genCount w i) : 2 * (gens w).card ≤ n := by
  have hs := sum_genCount w
  have : (gens w).card • 2 ≤ ∑ i ∈ gens w, genCount w i := by
    rw [← Finset.sum_const]
    exact Finset.sum_le_sum h
  rw [smul_eq_mul] at this
  omega

end PartS
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartS
theorem card_gens_le_half_of_three {d n : ℕ} (w : Fin n → Ltr d)
    (h : ∀ i ∈ gens w, 2 ≤ genCount w i) (i₀ : Fin d) (h₀ : 3 ≤ genCount w i₀) :
    2 * (gens w).card + 1 ≤ n := by
  classical
  have hi₀ : i₀ ∈ gens w := by
    unfold genCount at h₀
    obtain ⟨j, hj⟩ := Finset.card_pos.mp
      (by omega : 0 < (Finset.univ.filter fun j => (w j).1 = i₀).card)
    simp only [Finset.mem_filter] at hj
    rw [← hj.2]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hs := sum_genCount w
  rw [← Finset.add_sum_erase _ _ hi₀] at hs
  have hc := Finset.card_erase_add_one hi₀
  have : ((gens w).erase i₀).card • 2 ≤ ∑ x ∈ (gens w).erase i₀, genCount w x := by
    rw [← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => h i (Finset.mem_of_mem_erase hi)
  rw [smul_eq_mul] at this
  omega

end PartS
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartS
open Equiv
/-- A letter as a permutation. -/
def ltrPerm {d N : ℕ} (σ : Fin d → Perm (Fin N)) (l : Ltr d) : Perm (Fin N) :=
  if l.2 then (σ l.1)⁻¹ else σ l.1

theorem lift_ltrFG {d N : ℕ} (σ : Fin d → Perm (Fin N)) (l : Ltr d) :
    FreeGroup.lift σ (ltrFG l) = ltrPerm σ l := by
  unfold ltrFG ltrPerm
  split_ifs <;> simp

theorem wordPerm_eq {d N n : ℕ} (σ : Fin d → Perm (Fin N)) (w : Fin n → Ltr d) :
    wordPerm σ w = (List.ofFn fun j => ltrPerm σ (w j)).prod := by
  unfold wordPerm wordFG
  rw [map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext j
  simp [lift_ltrFG]

theorem wordFG_ne_one_of_genCount_eq_one {d n : ℕ} (w : Fin n → Ltr d) (i : Fin d)
    (hi : genCount w i = 1) : wordFG w ≠ 1 := by
  classical
  intro h
  obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp hi
  have hj0i : (w j0).1 = i := by
    have : j0 ∈ Finset.univ.filter fun j => (w j).1 = i := by rw [hj0]; simp
    simpa using this
  have huniq : ∀ j, (w j).1 = i → j = j0 := by
    intro j hj
    have : j ∈ Finset.univ.filter fun j => (w j).1 = i := by simpa using hj
    rw [hj0] at this
    simpa using this
  let φ : FreeGroup (Fin d) →* Multiplicative ℤ :=
    FreeGroup.lift fun j => if j = i then Multiplicative.ofAdd (1 : ℤ) else 1
  have h1 := congrArg φ h
  rw [map_one] at h1
  unfold wordFG at h1
  rw [map_list_prod, List.map_ofFn, List.prod_ofFn] at h1
  rw [Finset.prod_eq_single j0] at h1
  · simp only [Function.comp_apply, ltrFG, φ] at h1
    split_ifs at h1 <;> simp_all
  · intro j _ hj
    have hne : (w j).1 ≠ i := fun e => hj (huniq j e)
    simp only [Function.comp_apply, ltrFG, φ]
    split_ifs <;> simp_all
  · simp

end PartS
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
/-! ## Part E: expectations -/

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartS
open Equiv
theorem fixW_congr {d N n : ℕ} (w : Fin n → Ltr d) (σ τ : Fin d → Equiv.Perm (Fin N))
    (h : ∀ i, 0 < genCount w i → σ i = τ i) : fixW w σ = fixW w τ := by
  classical
  unfold fixW
  rw [wordPerm_eq, wordPerm_eq]
  congr 4
  funext j
  unfold ltrPerm
  rw [h (w j).1 (Finset.card_pos.mpr ⟨j, by simp⟩)]

end PartS
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartA
variable {X : Type*} [Fintype X]
lemma card_pos' [Nonempty X] : (0 : ℝ) < Fintype.card X := by
  exact_mod_cast Fintype.card_pos

lemma prob_le_one (E : X → Prop) : uniformProb E ≤ 1 := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_le_univ _

lemma prob_mono (E F : X → Prop) (h : ∀ x, E x → F x) : uniformProb E ≤ uniformProb F := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)

lemma prob_of_forall (E : X → Prop) [Nonempty X] (h : ∀ x, E x) : uniformProb E = 1 := by
  classical
  unfold uniformProb
  have : Finset.univ.filter E = Finset.univ := by
    ext x; simp [h x]
  rw [this, Finset.card_univ]
  exact div_self card_pos'.ne'

lemma prob_cover (E F : X → Prop) [Nonempty X] (h : ∀ x, E x ∨ F x) :
    1 ≤ uniformProb E + uniformProb F := by
  classical
  unfold uniformProb
  rw [← add_div, le_div_iff₀ card_pos', one_mul]
  have : Finset.univ ⊆ Finset.univ.filter E ∪ Finset.univ.filter F := by
    intro x _
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h x
  have h2 := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ] at h2
  exact_mod_cast h2

end PartA
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartA
lemma catalan_ge_one (p : ℕ) : 1 ≤ catalan p := by
  have h := succ_mul_catalan_eq_centralBinom p
  have : 0 < p.centralBinom := Nat.centralBinom_pos p
  rcases Nat.eq_zero_or_pos (catalan p) with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0

lemma four_pow_le_catalan (p : ℕ) :
    (4 : ℝ) ^ p ≤ (2 * p + 1) * (p + 1) * catalan p := by
  have h1 := Nat.four_pow_le_two_mul_add_one_mul_central_binom p
  have h2 := succ_mul_catalan_eq_centralBinom p
  rw [Nat.centralBinom_eq_two_mul_choose] at h2
  rw [← h2] at h1
  have : (4 ^ p : ℕ) ≤ (2 * p + 1) * (p + 1) * catalan p := by
    calc 4 ^ p ≤ (2 * p + 1) * ((p + 1) * catalan p) := h1
      _ = _ := by ring
  exact_mod_cast this

/-- `d^p ≤ retCount d (2p)` once `2p ≤ d`. -/
lemma pow_le_retCount (d p : ℕ) (hd : 2 * p ≤ d) :
    (d : ℝ) ^ p ≤ retCount d (2 * p) := by
  have h := retCount_ge d p (by omega)
  have hc : (1 : ℝ) ≤ catalan p := by exact_mod_cast catalan_ge_one p
  have hd' : (2 * p : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : (d : ℝ) ^ p ≤ 2 ^ p * ((d : ℝ) - p) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
  have h3 : (0 : ℝ) ≤ 2 ^ p * ((d : ℝ) - p) ^ p := le_trans (by positivity) h2
  calc (d : ℝ) ^ p ≤ 2 ^ p * ((d : ℝ) - p) ^ p := h2
    _ ≤ (catalan p : ℝ) * (2 ^ p * ((d : ℝ) - p) ^ p) := le_mul_of_one_le_left h3 hc
    _ = (catalan p : ℝ) * 2 ^ p * ((d : ℝ) - p) ^ p := by ring
    _ ≤ _ := h

end PartA
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartE
open Equiv

end PartE
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartS
open Equiv
/-- Splitting a word at the unique occurrence of generator `i`. -/
theorem wordPerm_update_split {d N n : ℕ} (w : Fin n → Ltr d) (i : Fin d) (j0 : Fin n)
    (hj0 : (w j0).1 = i) (huniq : ∀ j, (w j).1 = i → j = j0) (σ : Fin d → Perm (Fin N)) :
    ∃ A B : Perm (Fin N), ∀ τ : Perm (Fin N),
      wordPerm (Function.update σ i τ) w = A * (if (w j0).2 then τ⁻¹ else τ) * B := by
  classical
  let L : (Fin d → Perm (Fin N)) → List (Perm (Fin N)) := fun σ =>
    List.ofFn fun j => ltrPerm σ (w j)
  refine ⟨((L σ).take j0).prod, ((L σ).drop (j0 + 1)).prod, fun τ => ?_⟩
  set σ' := Function.update σ i τ
  have hlen : ∀ s, (L s).length = n := fun s => by simp [L]
  have key : ∀ k : Fin n, k ≠ j0 → ltrPerm σ' (w k) = ltrPerm σ (w k) := by
    intro k hne
    have : (w k).1 ≠ i := fun e => hne (huniq _ e)
    unfold ltrPerm
    simp only [σ', Function.update_of_ne this]
  have hj0lt : (j0 : ℕ) < (L σ').length := by rw [hlen]; exact j0.2
  have hsplit : L σ' = (L σ').take j0 ++ (L σ')[(j0 : ℕ)] :: (L σ').drop (j0 + 1) := by
    conv_lhs => rw [← List.take_append_drop (j0 : ℕ) (L σ')]
    rw [List.drop_eq_getElem_cons hj0lt]
  have htake : (L σ').take j0 = (L σ).take j0 := by
    apply List.ext_getElem
    · simp [hlen]
    · intro k h1 h2
      simp only [List.getElem_take, L, List.getElem_ofFn]
      simp only [List.length_take, hlen] at h1
      exact key ⟨k, by omega⟩ (by intro e; rw [Fin.ext_iff] at e; simp at e; omega)
  have hdrop : (L σ').drop (j0 + 1) = (L σ).drop (j0 + 1) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro k h1 h2
      simp only [List.getElem_drop, L, List.getElem_ofFn]
      simp only [List.length_drop, hlen] at h1
      exact key ⟨_, by omega⟩ (by intro e; rw [Fin.ext_iff] at e; simp at e; omega)
  have hmid : (L σ')[(j0 : ℕ)] = if (w j0).2 then τ⁻¹ else τ := by
    simp only [L, List.getElem_ofFn, ltrPerm, σ']
    rw [hj0, Function.update_self]
  rw [wordPerm_eq]
  change (L σ').prod = _
  rw [hsplit, List.prod_append, List.prod_cons, htake, hdrop, hmid, mul_assoc]

theorem exists_UV {N : ℕ} (A B : Perm (Fin N)) (ε : Bool) :
    ∃ U V : Perm (Fin N), ∀ τ : Perm (Fin N), ∀ x,
      ((A * (if ε then τ⁻¹ else τ) * B) x = x ↔ τ (U x) = V x) := by
  cases ε
  · refine ⟨B, A⁻¹, fun τ x => ?_⟩
    simp only [Bool.false_eq_true, if_false, Perm.mul_apply]
    rw [Perm.eq_inv_iff_eq]
  · refine ⟨A⁻¹, B, fun τ x => ?_⟩
    simp only [if_true, Perm.mul_apply]
    rw [← Perm.eq_inv_iff_eq (f := A), Perm.inv_eq_iff_eq, eq_comm]

theorem card_perm_apply_eq {N : ℕ} (hN : 1 ≤ N) (u v : Fin N) :
    (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v).card = (N - 1).factorial := by
  classical
  have hconst : ∀ v v' : Fin N, (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v).card =
      (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v').card := by
    intro v v'
    apply Finset.card_bij' (fun τ _ => swap v v' * τ) (fun τ _ => swap v v' * τ)
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [Perm.mul_apply, hτ, swap_apply_left]
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [Perm.mul_apply, hτ, swap_apply_right]
    · intro τ _; simp [← mul_assoc]
    · intro τ _; simp [← mul_assoc]
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Perm (Fin N))))
    (t := (Finset.univ : Finset (Fin N))) (f := fun τ => τ u) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  rw [Finset.sum_congr rfl (fun v' _ => (hconst v v').symm), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have h2 := Nat.mul_factorial_pred (n := N) (by omega)
  have : N * (N - 1).factorial = N * (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v).card := by
    rw [h2, hsum]
  exact (Nat.eq_of_mul_eq_mul_left (by omega) this).symm

theorem card_perm_apply_eq_two {N : ℕ} (hN : 2 ≤ N) (u u' v v' : Fin N) (hu : u ≠ u') :
    (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v ∧ τ u' = v').card ≤
      (N - 2).factorial := by
  classical
  by_cases hv : v = v'
  · subst hv
    have : (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v ∧ τ u' = v) = ∅ := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      intro h1 h2
      exact hu (τ.injective (h1.trans h2.symm))
    simp [this]
  have hconst : ∀ v'', v'' ≠ v →
      (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v ∧ τ u' = v'').card =
      (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v ∧ τ u' = v').card := by
    intro v'' hv''
    apply Finset.card_bij' (fun τ _ => swap v' v'' * τ) (fun τ _ => swap v' v'' * τ)
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [Perm.mul_apply, Perm.mul_apply, hτ.1, hτ.2]
      exact ⟨swap_apply_of_ne_of_ne hv (Ne.symm hv''), swap_apply_right _ _⟩
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [Perm.mul_apply, Perm.mul_apply, hτ.1, hτ.2]
      exact ⟨swap_apply_of_ne_of_ne hv (Ne.symm hv''), swap_apply_left _ _⟩
    · intro τ _; simp [← mul_assoc]
    · intro τ _; simp [← mul_assoc]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun τ : Perm (Fin N) => τ u = v)
    (t := (Finset.univ : Finset (Fin N))) (f := fun τ => τ u') (fun _ _ => Finset.mem_univ _)
  simp only [Finset.filter_filter] at hsum
  rw [card_perm_apply_eq (by omega) u v,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at hsum
  have hzero : (Finset.univ.filter fun τ : Perm (Fin N) => τ u = v ∧ τ u' = v).card = 0 := by
    rw [Finset.card_eq_zero]
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_and]
    intro h1 h2
    exact hu (τ.injective (h1.trans h2.symm))
  rw [hzero, zero_add, Finset.sum_congr rfl (fun v'' hv'' => hconst v'' (Finset.ne_of_mem_erase hv'')),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  have h2 : (N - 1).factorial = (N - 1) * (N - 2).factorial := by
    have := Nat.mul_factorial_pred (n := N - 1) (by omega)
    rw [show N - 1 - 1 = N - 2 by omega] at this
    exact this.symm
  rw [h2] at hsum
  exact (Nat.eq_of_mul_eq_mul_left (by omega) hsum).symm.le

theorem sum_fixCount {N : ℕ} (hN : 1 ≤ N) (A B : Perm (Fin N)) (ε : Bool) :
    ∑ τ : Perm (Fin N), fixCount (A * (if ε then τ⁻¹ else τ) * B) = N.factorial := by
  classical
  obtain ⟨U, V, hUV⟩ := exists_UV A B ε
  unfold fixCount
  simp_rw [hUV, Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter, card_perm_apply_eq hN]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_factorial_pred (by omega)]

theorem sum_fixCount_mul {N : ℕ} (hN : 2 ≤ N) (A B A' B' : Perm (Fin N)) (ε ε' : Bool) :
    ∑ τ : Perm (Fin N), fixCount (A * (if ε then τ⁻¹ else τ) * B) *
      fixCount (A' * (if ε' then τ⁻¹ else τ) * B') ≤ 3 * N.factorial := by
  classical
  obtain ⟨U, V, hUV⟩ := exists_UV A B ε
  obtain ⟨U', V', hUV'⟩ := exists_UV A' B' ε'
  unfold fixCount
  simp_rw [hUV, hUV', Finset.card_filter, Finset.sum_mul_sum]
  have hterm : ∀ x y, ∑ τ : Perm (Fin N), (if τ (U x) = V x then 1 else 0) *
      (if τ (U' y) = V' y then 1 else 0) ≤
      (if U'⁻¹ (U x) = y then (N - 1).factorial else 0) + (N - 2).factorial := by
    intro x y
    have : ∑ τ : Perm (Fin N), (if τ (U x) = V x then 1 else 0) *
        (if τ (U' y) = V' y then 1 else 0) =
        (Finset.univ.filter fun τ : Perm (Fin N) => τ (U x) = V x ∧ τ (U' y) = V' y).card := by
      rw [Finset.card_filter]
      congr 1; funext τ
      split_ifs <;> simp_all
    rw [this]
    by_cases hxy : U'⁻¹ (U x) = y
    · rw [if_pos hxy]
      refine le_trans ?_ (Nat.le_add_right _ _)
      rw [← card_perm_apply_eq (by omega) (U x) (V x)]
      exact Finset.card_le_card fun τ hτ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        exact hτ.1
    · rw [if_neg hxy, zero_add]
      apply card_perm_apply_eq_two hN
      intro e
      apply hxy
      rw [e]; simp
  calc _ = ∑ x, ∑ y, ∑ τ : Perm (Fin N), (if τ (U x) = V x then 1 else 0) *
        (if τ (U' y) = V' y then 1 else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ ≤ ∑ x : Fin N, ∑ y : Fin N,
          ((if U'⁻¹ (U x) = y then (N - 1).factorial else 0) + (N - 2).factorial) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = N * ((N - 1).factorial + N * (N - 2).factorial) := by
        simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
    _ ≤ 3 * N.factorial := by
        obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
        simp only [show M + 2 - 1 = M + 1 by omega, show M + 2 - 2 = M by omega,
          Nat.factorial_succ]
        have h0 := Nat.zero_le ((M + 2) * M * M.factorial)
        ring_nf
        ring_nf at h0
        nlinarith

/-- Averaging over `σ i`. -/
theorem sum_mul_factorial {d N : ℕ} (i : Fin d) (f : (Fin d → Perm (Fin N)) → ℝ) :
    (∑ σ, f σ) * (N.factorial : ℝ) = ∑ σ, ∑ τ : Perm (Fin N), f (Function.update σ i τ) := by
  classical
  let e : Perm (Fin N) → (Fin d → Perm (Fin N)) ≃ (Fin d → Perm (Fin N)) := fun π =>
    { toFun := fun σ => Function.update σ i (π * σ i)
      invFun := fun σ => Function.update σ i (π⁻¹ * σ i)
      left_inv := fun σ => by simp
      right_inv := fun σ => by simp }
  have h1 : ∀ π, ∑ σ, f σ = ∑ σ, f (Function.update σ i (π * σ i)) :=
    fun π => (Equiv.sum_comp (e π) f).symm
  have hcard : (N.factorial : ℝ) = ∑ _π : Perm (Fin N), (1 : ℝ) := by
    simp [Fintype.card_perm]
  rw [hcard, Finset.mul_sum]
  simp_rw [mul_one]
  rw [Finset.sum_congr rfl (fun π _ => h1 π), Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact Fintype.sum_equiv (Equiv.mulRight (σ i)) _ _ (fun π => rfl)

theorem exists_j0 {d n : ℕ} (w : Fin n → Ltr d) (i : Fin d) (hi : genCount w i = 1) :
    ∃ j0, (w j0).1 = i ∧ ∀ j, (w j).1 = i → j = j0 := by
  classical
  obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp hi
  refine ⟨j0, ?_, ?_⟩
  · have : j0 ∈ Finset.univ.filter fun j => (w j).1 = i := by rw [hj0]; simp
    simpa using this
  · intro j hj
    have : j ∈ Finset.univ.filter fun j => (w j).1 = i := by simpa using hj
    rw [hj0] at this
    simpa using this

theorem sum_fixW_update {d N n : ℕ} (hN : 1 ≤ N) (w : Fin n → Ltr d) (i : Fin d)
    (hi : genCount w i = 1) (σ : Fin d → Perm (Fin N)) :
    ∑ τ : Perm (Fin N), fixW w (Function.update σ i τ) = N.factorial := by
  obtain ⟨j0, hj0, huniq⟩ := exists_j0 w i hi
  obtain ⟨A, B, hAB⟩ := wordPerm_update_split w i j0 hj0 huniq σ
  unfold fixW
  simp_rw [hAB]
  rw [← Nat.cast_sum, sum_fixCount hN]

theorem uniformExp_fixW_sub_one_mul {d N n : ℕ} (hN : 1 ≤ N) (w : Fin n → Ltr d) (i : Fin d)
    (hi : genCount w i = 1) (g : (Fin d → Equiv.Perm (Fin N)) → ℝ)
    (hg : ∀ σ τ : Fin d → Equiv.Perm (Fin N), (∀ j, j ≠ i → σ j = τ j) → g σ = g τ) :
    uniformExp (fun σ => (fixW w σ - 1) * g σ) = 0 := by
  unfold uniformExp
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have : (∑ σ, (fixW w σ - 1) * g σ) * (N.factorial : ℝ) = 0 := by
    rw [sum_mul_factorial i]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have hg' : ∀ τ, g (Function.update σ i τ) = g σ := fun τ =>
      hg _ _ fun j hj => Function.update_of_ne hj _ _
    simp_rw [hg', ← Finset.sum_mul, Finset.sum_sub_distrib, sum_fixW_update hN w i hi]
    simp [Fintype.card_perm]
  rw [(mul_eq_zero.mp this).resolve_right hfac, zero_div]

end PartS
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartS
open Equiv
theorem uniformExp_fixW_mul_le {d N n : ℕ} (hN : 2 ≤ N) (w w' : Fin n → Ltr d) (i : Fin d)
    (hi : genCount w i = 1) (hi' : genCount w' i = 1) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => fixW w σ * fixW w' σ) ≤ 3 := by
  unfold uniformExp
  have hfac : (0 : ℝ) < N.factorial := by positivity
  have hcard : (0 : ℝ) < Fintype.card (Fin d → Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hcard]
  have : (∑ σ : Fin d → Perm (Fin N), fixW w σ * fixW w' σ) * (N.factorial : ℝ) ≤
      (3 * Fintype.card (Fin d → Perm (Fin N))) * N.factorial := by
    rw [sum_mul_factorial i]
    have hb : ∀ σ : Fin d → Perm (Fin N),
        ∑ τ : Perm (Fin N), fixW w (Function.update σ i τ) * fixW w' (Function.update σ i τ) ≤
          3 * N.factorial := by
      intro σ
      obtain ⟨j0, hj0, huniq⟩ := exists_j0 w i hi
      obtain ⟨A, B, hAB⟩ := wordPerm_update_split w i j0 hj0 huniq σ
      obtain ⟨j0', hj0', huniq'⟩ := exists_j0 w' i hi'
      obtain ⟨A', B', hAB'⟩ := wordPerm_update_split w' i j0' hj0' huniq' σ
      unfold fixW
      simp_rw [hAB, hAB', ← Nat.cast_mul]
      rw [← Nat.cast_sum]
      exact_mod_cast sum_fixCount_mul hN A B A' B' _ _
    calc ∑ σ, ∑ τ : Perm (Fin N),
          fixW w (Function.update σ i τ) * fixW w' (Function.update σ i τ)
        ≤ ∑ _σ : Fin d → Perm (Fin N), 3 * (N.factorial : ℝ) := Finset.sum_le_sum fun σ _ => hb σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have := le_of_mul_le_mul_right this hfac
  linarith

end PartS
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartS
open Equiv
/-! ## Part S -/
theorem uniformProb_le_neg_le {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) {t : ℝ}
    (ht : 0 < t) : uniformProb (fun x => f x ≤ -t) ≤ uniformExp (fun x => f x ^ 2) / t ^ 2 := by
  classical
  unfold uniformProb uniformExp
  have hK : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have key : ((Finset.univ.filter fun x => f x ≤ -t).card : ℝ) * t ^ 2 ≤ ∑ x, f x ^ 2 := by
    calc ((Finset.univ.filter fun x => f x ≤ -t).card : ℝ) * t ^ 2
        = ∑ x ∈ Finset.univ.filter (fun x => f x ≤ -t), t ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x => f x ≤ -t), f x ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          nlinarith
      _ ≤ ∑ x, f x ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun x _ _ => sq_nonneg _)
  rw [div_div, le_div_iff₀ (by positivity)]
  calc ((Finset.univ.filter fun x => f x ≤ -t).card : ℝ) / Fintype.card X *
        (Fintype.card X * t ^ 2)
      = ((Finset.univ.filter fun x => f x ≤ -t).card : ℝ) * t ^ 2 := by
        field_simp
    _ ≤ _ := key

theorem mem_gens_iff {d n : ℕ} (w : Fin n → Ltr d) (i : Fin d) :
    i ∈ gens w ↔ 0 < genCount w i := by
  classical
  unfold gens genCount
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  · intro h
    obtain ⟨j, hj⟩ := Finset.card_pos.mp h
    simp only [Finset.mem_filter] at hj
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.2⟩

theorem fixW_nonneg {d N n : ℕ} (w : Fin n → Ltr d) (σ : Fin d → Perm (Fin N)) :
    0 ≤ fixW w σ := by unfold fixW; positivity

theorem fixW_le {d N n : ℕ} (w : Fin n → Ltr d) (σ : Fin d → Perm (Fin N)) :
    fixW w σ ≤ N := by
  unfold fixW fixCount
  have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun x => wordPerm σ w x = x)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

theorem fixW_of_wordFG_eq_one {d N n : ℕ} (w : Fin n → Ltr d) (σ : Fin d → Perm (Fin N))
    (h : wordFG w = 1) : fixW w σ = N := by
  unfold fixW fixCount wordPerm
  rw [h, map_one]
  simp

open Classical in
/-- Words without a once-generator are few. -/
theorem card_not_hasOnce_le (d p : ℕ) :
    ((Finset.univ.filter fun w : Fin (2 * p) → Ltr d => ¬ HasOnce w).card : ℝ) ≤
      (2 * p : ℝ) ^ (2 * p) * (d : ℝ) ^ p := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin (2 * p) → Ltr 0))
      (fun w => ¬ HasOnce w)
    rw [Finset.card_univ] at h1
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      zero_mul] at h1
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp only [mul_zero, pow_zero] at h1 ⊢
      norm_num
      exact_mod_cast h1
    · rw [zero_pow (by omega)] at h1
      have : (Finset.univ.filter fun w : Fin (2 * p) → Ltr 0 => ¬ HasOnce w).card = 0 := by omega
      rw [this]
      simp only [Nat.cast_zero]
      rw [zero_pow (by omega : p ≠ 0)]
      simp
  · refine le_trans ?_ (card_gens_le d (2 * p) p hd)
    refine Nat.cast_le.mpr (Finset.card_le_card fun w hw => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have h2 : ∀ i ∈ gens w, 2 ≤ genCount w i := by
      intro i hi
      have := (mem_gens_iff w i).mp hi
      by_contra hlt
      exact hw ⟨i, by omega⟩
    have := card_gens_le_half w h2
    omega

theorem trMoment_ge {d N p : ℕ} (hN : 1 ≤ N) (σ : Fin d → Equiv.Perm (Fin N)) :
    ((N : ℝ) - 1) * retCount d (2 * p) + onceSum (2 * p) σ - (2 * p : ℝ) ^ (2 * p) * (d : ℝ) ^ p ≤
      trMoment (2 * p) σ := by
  classical
  unfold trMoment onceSum
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : Fin (2 * p) → Ltr d => HasOnce w)]
  have hterm : ∀ w ∈ Finset.univ.filter (fun w : Fin (2 * p) → Ltr d => ¬ HasOnce w),
      ((N : ℝ) - 1) * (if wordFG w = 1 then 1 else 0) - 1 ≤ fixW w σ - 1 := by
    intro w _
    split_ifs with h
    · rw [fixW_of_wordFG_eq_one w σ h]; linarith
    · have := fixW_nonneg w σ; linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.filter_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hret : (Finset.univ.filter fun w : Fin (2 * p) → Ltr d => ¬ HasOnce w ∧ wordFG w = 1) =
      Finset.univ.filter fun w : Fin (2 * p) → Ltr d => wordFG w = 1 := by
    apply Finset.filter_congr
    intro w _
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro ⟨i, hi⟩
      exact wordFG_ne_one_of_genCount_eq_one w i hi h
  rw [hret] at hsum
  have hc := card_not_hasOnce_le d p
  unfold retCount
  have hN' : (0 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  linarith

theorem uniformExp_le_const {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (c : ℝ)
    (h : ∀ x, f x ≤ c) : uniformExp f ≤ c := by
  unfold uniformExp
  have hK : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hK]
  calc ∑ x, f x ≤ ∑ _x : X, c := Finset.sum_le_sum fun x _ => h x
    _ = c * Fintype.card X := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem genCount_append {d n m : ℕ} (w : Fin n → Ltr d) (w' : Fin m → Ltr d) (i : Fin d) :
    genCount (Fin.append w w') i = genCount w i + genCount w' i := by
  classical
  unfold genCount
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Every generator occurring occurs at least twice. -/
def P2 {d n : ℕ} (v : Fin n → Ltr d) : Prop := ∀ i ∈ gens v, 2 ≤ genCount v i

open Classical in
theorem term_le {d N n : ℕ} (hN : 2 ≤ N) (w w' : Fin n → Ltr d) (hw : HasOnce w) :
    uniformExp (fun σ : Fin d → Perm (Fin N) => (fixW w σ - 1) * (fixW w' σ - 1)) ≤
      (if P2 (Fin.append w w') then (2 : ℝ) else 0) +
      (if P2 (Fin.append w w') ∧ ∃ i, 3 ≤ genCount (Fin.append w w') i then (N : ℝ) ^ 2
        else 0) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hbound : uniformExp (fun σ : Fin d → Perm (Fin N) =>
      (fixW w σ - 1) * (fixW w' σ - 1)) ≤ (N : ℝ) ^ 2 := by
    apply uniformExp_le_const
    intro σ
    have a0 := fixW_nonneg w σ
    have a1 := fixW_le w σ
    have b0 := fixW_nonneg w' σ
    have b1 := fixW_le w' σ
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ fixW w σ) (by linarith : (0 : ℝ) ≤ N - fixW w' σ)]
  have hZ : ∀ (u u' : Fin n → Ltr d) (i : Fin d), genCount u i = 1 → genCount u' i = 0 →
      uniformExp (fun σ : Fin d → Perm (Fin N) => (fixW u σ - 1) * (fixW u' σ - 1)) = 0 := by
    intro u u' i hu hu'
    apply uniformExp_fixW_sub_one_mul hN1 u i hu (fun σ => fixW u' σ - 1)
    intro σ τ hστ
    rw [fixW_congr u' σ τ fun j hj => hστ j (by rintro rfl; omega)]
  set v := Fin.append w w'
  by_cases h2 : P2 v
  · by_cases h3 : ∃ i, 3 ≤ genCount v i
    · simp only [h2, h3, and_self, if_true]
      linarith
    · simp only [h2, h3, and_false, if_true, if_false, add_zero]
      obtain ⟨i, hi⟩ := hw
      have hv : genCount v i = genCount w i + genCount w' i := genCount_append w w' i
      have hmem : i ∈ gens v := (mem_gens_iff v i).mpr (by omega)
      have := h2 i hmem
      have h3' : ¬ 3 ≤ genCount v i := fun h => h3 ⟨i, h⟩
      have hi' : genCount w' i = 1 := by omega
      have hm := uniformExp_fixW_mul_le hN w w' i hi hi'
      have e1 := uniformExp_fixW_sub_one_mul hN1 w i hi (fun _ => 1) (fun _ _ _ => rfl)
      have e2 := uniformExp_fixW_sub_one_mul hN1 w' i hi' (fun _ => 1) (fun _ _ _ => rfl)
      unfold uniformExp at *
      have eq : ∀ σ : Fin d → Perm (Fin N), (fixW w σ - 1) * (fixW w' σ - 1) =
          fixW w σ * fixW w' σ - (fixW w σ - 1) * 1 - (fixW w' σ - 1) * 1 - 1 := by
        intro σ; ring
      simp_rw [eq, Finset.sum_sub_distrib, sub_div]
      have hK : (0 : ℝ) < Fintype.card (Fin d → Perm (Fin N)) := by
        exact_mod_cast Fintype.card_pos
      have : (∑ _x : Fin d → Perm (Fin N), (1 : ℝ)) / Fintype.card (Fin d → Perm (Fin N)) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_self hK.ne']
      rw [this]
      linarith
  · simp only [h2, false_and, if_false, add_zero]
    unfold P2 at h2
    push Not at h2
    obtain ⟨i, hmem, hlt⟩ := h2
    have hpos := (mem_gens_iff v i).mp hmem
    have hv : genCount v i = genCount w i + genCount w' i := genCount_append w w' i
    rcases (by omega : (genCount w i = 1 ∧ genCount w' i = 0) ∨
        (genCount w' i = 1 ∧ genCount w i = 0)) with ⟨a, b⟩ | ⟨a, b⟩
    · rw [hZ w w' i a b]
    · have := hZ w' w i a b
      simp_rw [mul_comm (fixW w _ - 1)]
      rw [this]

theorem append_injective {d n m : ℕ} :
    Function.Injective (fun x : (Fin n → Ltr d) × (Fin m → Ltr d) => Fin.append x.1 x.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only at h
  have h1 : a = a' := by
    funext j
    have := congrFun h (Fin.castAdd m j)
    simpa [Fin.append_left] using this
  have h2 : b = b' := by
    funext j
    have := congrFun h (Fin.natAdd n j)
    simpa [Fin.append_right] using this
  rw [h1, h2]

theorem uniformExp_onceSum_sq_le {d N p : ℕ} (hN : 2 ≤ N) (hp : 1 ≤ p) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => onceSum (2 * p) σ ^ 2) ≤
      2 * (4 * p : ℝ) ^ (4 * p) * (d : ℝ) ^ (2 * p) +
        (N : ℝ) ^ 2 * (4 * p : ℝ) ^ (4 * p) * (d : ℝ) ^ (2 * p - 1) := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsEmpty (Fin (2 * p) → Ltr 0) := ⟨fun w => (w ⟨0, by omega⟩).1.elim0⟩
    have h0 : ∀ σ : Fin 0 → Perm (Fin N), onceSum (2 * p) σ = 0 := by
      intro σ
      unfold onceSum
      simp
    simp_rw [h0]
    unfold uniformExp
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      zero_div]
    positivity
  -- expand the square
  set O := Finset.univ.filter fun w : Fin (2 * p) → Ltr d => HasOnce w with hO
  have hexp : uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => onceSum (2 * p) σ ^ 2) =
      ∑ w ∈ O, ∑ w' ∈ O,
        uniformExp (fun σ : Fin d → Perm (Fin N) => (fixW w σ - 1) * (fixW w' σ - 1)) := by
    unfold uniformExp onceSum
    simp only [sq, Finset.sum_mul_sum, ← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm]
  rw [hexp]
  let F : (Fin (2 * p + 2 * p) → Ltr d) → ℝ := fun v =>
    (if P2 v then (2 : ℝ) else 0) +
      (if P2 v ∧ ∃ i, 3 ≤ genCount v i then (N : ℝ) ^ 2 else 0)
  have hF0 : ∀ v, 0 ≤ F v := fun v => by
    simp only [F]; split_ifs <;> positivity
  have step1 : ∑ w ∈ O, ∑ w' ∈ O,
      uniformExp (fun σ : Fin d → Perm (Fin N) => (fixW w σ - 1) * (fixW w' σ - 1)) ≤
      ∑ w ∈ O, ∑ w' ∈ O, F (Fin.append w w') := by
    refine Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun w' _ => ?_
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact term_le hN w w' hw
  have step2 : ∑ w ∈ O, ∑ w' ∈ O, F (Fin.append w w') ≤ ∑ v, F v := by
    calc ∑ w ∈ O, ∑ w' ∈ O, F (Fin.append w w')
        ≤ ∑ w, ∑ w', F (Fin.append w w') := by
          refine le_trans (Finset.sum_le_sum fun w _ =>
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ O)
              (fun _ _ _ => hF0 _)) ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ O)
              (fun _ _ _ => Finset.sum_nonneg fun _ _ => hF0 _)
      _ = ∑ x ∈ (Finset.univ : Finset ((Fin (2 * p) → Ltr d) × (Fin (2 * p) → Ltr d))),
            F (Fin.append x.1 x.2) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ v ∈ Finset.univ.image
            (fun x : (Fin (2 * p) → Ltr d) × (Fin (2 * p) → Ltr d) => Fin.append x.1 x.2),
            F v := by
          rw [Finset.sum_image fun x _ y _ h => append_injective h]
      _ ≤ ∑ v, F v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => hF0 _)
  have step3 : ∑ v, F v =
      2 * ((Finset.univ.filter fun v : Fin (2 * p + 2 * p) → Ltr d => P2 v).card : ℝ) +
      (N : ℝ) ^ 2 * ((Finset.univ.filter fun v : Fin (2 * p + 2 * p) → Ltr d =>
        P2 v ∧ ∃ i, 3 ≤ genCount v i).card : ℝ) := by
    simp only [F, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hc1 : ((Finset.univ.filter fun v : Fin (2 * p + 2 * p) → Ltr d => P2 v).card : ℝ) ≤
      (4 * p : ℝ) ^ (4 * p) * (d : ℝ) ^ (2 * p) := by
    refine le_trans ?_ ((card_gens_le d (2 * p + 2 * p) (2 * p) hd).trans (le_of_eq ?_))
    · refine Nat.cast_le.mpr (Finset.card_le_card fun v hv => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have := card_gens_le_half v hv
      omega
    · rw [show 2 * p + 2 * p = 4 * p by ring]
      push_cast
      ring
  have hc2 : ((Finset.univ.filter fun v : Fin (2 * p + 2 * p) → Ltr d =>
        P2 v ∧ ∃ i, 3 ≤ genCount v i).card : ℝ) ≤
      (4 * p : ℝ) ^ (4 * p) * (d : ℝ) ^ (2 * p - 1) := by
    refine le_trans ?_ ((card_gens_le d (2 * p + 2 * p) (2 * p - 1) hd).trans ?_)
    · refine Nat.cast_le.mpr (Finset.card_le_card fun v hv => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      obtain ⟨h2, i, hi⟩ := hv
      have := card_gens_le_half_of_three v h2 i hi
      omega
    · rw [show 2 * p + 2 * p = 4 * p by ring]
      have : ((2 * p - 1 : ℕ) : ℝ) ≤ 2 * p := by
        have : 2 * p - 1 ≤ 2 * p := Nat.sub_le _ _
        exact_mod_cast this
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)
      linarith
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  calc _ ≤ ∑ v, F v := step1.trans step2
    _ = _ := step3
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hc2 hN2
      nlinarith

end PartS
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
/-! ## Part S: the second moment of the once-letter part -/
alias uniformExp_onceSum_sq_le := StrongConv.HighDeg.PartS.uniformExp_onceSum_sq_le

alias trMoment_ge := StrongConv.HighDeg.PartS.trMoment_ge

alias uniformProb_le_neg_le := StrongConv.HighDeg.PartS.uniformProb_le_neg_le

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartA
/-- The pointwise Chebyshev estimate. -/
lemma key_bound (p : ℕ) (hp : 1 ≤ p) (N d : ℕ) (hN : 2 ≤ N) (hd : 2 * p ≤ d)
    (hNc : 4 * (2 * p : ℝ) ^ (2 * p) ≤ (N : ℝ) - 1) :
    1 - 16 * (4 * p : ℝ) ^ (4 * p) * (2 / ((N : ℝ) - 1) ^ 2 + 4 / d) ≤
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ((N : ℝ) - 1) * retCount d (2 * p) / 2 ≤ trMoment (2 * p) σ) := by
  set K : ℝ := (retCount d (2 * p) : ℝ) with hKdef
  set C : ℝ := (4 * p : ℝ) ^ (4 * p) with hC
  set c : ℝ := (2 * p : ℝ) ^ (2 * p) with hc
  have hK : (d : ℝ) ^ p ≤ K := pow_le_retCount d p hd
  have hdpos : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
    linarith
  have hdp : (0 : ℝ) < (d : ℝ) ^ p := pow_pos hdpos _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hn : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set t : ℝ := ((N : ℝ) - 1) * K / 4 with ht
  have htpos : 0 < t := by
    have : 0 < K := lt_of_lt_of_le hdp hK
    positivity
  -- failure implies a large negative deviation of `onceSum`
  have hfail : ∀ σ : Fin d → Equiv.Perm (Fin N),
      ¬ (((N : ℝ) - 1) * K / 2 ≤ trMoment (2 * p) σ) → onceSum (2 * p) σ ≤ -t := by
    intro σ hσ
    rw [not_le] at hσ
    have h1 := trMoment_ge (p := p) (by omega : 1 ≤ N) σ
    have h2 : c * (d : ℝ) ^ p ≤ ((N : ℝ) - 1) * (d : ℝ) ^ p / 4 := by
      have := mul_le_mul_of_nonneg_right hNc hdp.le
      linarith
    have h3 : ((N : ℝ) - 1) * (d : ℝ) ^ p ≤ ((N : ℝ) - 1) * K :=
      mul_le_mul_of_nonneg_left hK hn.le
    rw [ht]
    linarith
  have hcheb := uniformProb_le_neg_le (fun σ : Fin d → Equiv.Perm (Fin N) => onceSum (2 * p) σ)
    htpos
  have hE := uniformExp_onceSum_sq_le (d := d) (N := N) hN hp
  have hmono := prob_mono (fun σ : Fin d → Equiv.Perm (Fin N) =>
      ¬ (((N : ℝ) - 1) * K / 2 ≤ trMoment (2 * p) σ))
    (fun σ => onceSum (2 * p) σ ≤ -t) hfail
  have hcov := prob_cover (fun σ : Fin d → Equiv.Perm (Fin N) =>
      ((N : ℝ) - 1) * K / 2 ≤ trMoment (2 * p) σ)
    (fun σ => ¬ (((N : ℝ) - 1) * K / 2 ≤ trMoment (2 * p) σ)) (fun σ => em _)
  -- bound E / t²
  set D' : ℝ := (d : ℝ) ^ (2 * p - 1) with hD'
  have hD : (d : ℝ) ^ (2 * p) = d * D' := by
    rw [hD', ← pow_succ']
    congr 1; omega
  have hD'pos : 0 < D' := pow_pos hdpos _
  have hCpos : 0 < C := by positivity
  have ht2 : ((N : ℝ) - 1) ^ 2 * (d * D') / 16 ≤ t ^ 2 := by
    rw [← hD, ht, pow_mul']
    have : ((N : ℝ) - 1) * (d : ℝ) ^ p / 4 ≤ ((N : ℝ) - 1) * K / 4 := by
      have := mul_le_mul_of_nonneg_left hK hn.le
      linarith
    have h0 : 0 ≤ ((N : ℝ) - 1) * (d : ℝ) ^ p / 4 := by positivity
    have := pow_le_pow_left₀ h0 this 2
    calc ((N : ℝ) - 1) ^ 2 * ((d : ℝ) ^ p) ^ 2 / 16 = (((N : ℝ) - 1) * (d : ℝ) ^ p / 4) ^ 2 := by
          ring
      _ ≤ _ := this
  have hNsq : (N : ℝ) ^ 2 ≤ 4 * ((N : ℝ) - 1) ^ 2 := by nlinarith
  have hbound : uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => onceSum (2 * p) σ ^ 2) / t ^ 2
      ≤ 16 * C * (2 / ((N : ℝ) - 1) ^ 2 + 4 / d) := by
    have hpos : 0 < ((N : ℝ) - 1) ^ 2 * (d * D') / 16 := by positivity
    have hEnn : 0 ≤ uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => onceSum (2 * p) σ ^ 2) := by
      unfold uniformExp
      exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
    calc _ ≤ uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => onceSum (2 * p) σ ^ 2) /
          (((N : ℝ) - 1) ^ 2 * (d * D') / 16) := div_le_div_of_nonneg_left hEnn hpos ht2
      _ ≤ (2 * C * (d * D') + (N : ℝ) ^ 2 * C * D') / (((N : ℝ) - 1) ^ 2 * (d * D') / 16) := by
          apply div_le_div_of_nonneg_right _ hpos.le
          rw [← hD]; exact hE
      _ ≤ _ := by
          rw [div_le_iff₀ hpos]
          have e : 16 * C * (2 / ((N : ℝ) - 1) ^ 2 + 4 / d) * (((N : ℝ) - 1) ^ 2 * (d * D') / 16)
              = 2 * C * (d * D') + 4 * ((N : ℝ) - 1) ^ 2 * C * D' := by
            field_simp
          rw [e]
          have := mul_le_mul_of_nonneg_right hNsq (mul_nonneg hCpos.le hD'pos.le)
          nlinarith
  linarith

/-- Part A. The probability of the good event `T(σ) ≥ (N − 1)K/2` tends to one. -/
theorem tendsto_prob_trMoment_ge (d : ℕ → ℕ) (hd : Tendsto (fun N => (d N : ℝ)) atTop atTop)
    (p : ℕ) (hp : 1 ≤ p) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin (d N) → Equiv.Perm (Fin N) =>
      ((N : ℝ) - 1) * retCount (d N) (2 * p) / 2 ≤ trMoment (2 * p) σ)) atTop (𝓝 1) := by
  set C : ℝ := (4 * p : ℝ) ^ (4 * p)
  have hNm : Tendsto (fun N : ℕ => (N : ℝ) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N : ℕ => 1 - 16 * C * (2 / ((N : ℝ) - 1) ^ 2 + 4 / (d N : ℝ)))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => 2 / ((N : ℝ) - 1) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hNm)
    have h2 : Tendsto (fun N : ℕ => 4 / (d N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hd
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := 16 * C)).mul (h1.add h2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hb tendsto_const_nhds ?_
    (Eventually.of_forall fun N => prob_le_one _)
  have e1 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have e2 : ∀ᶠ N : ℕ in atTop, (2 * p : ℝ) ≤ d N := hd.eventually_ge_atTop _
  have e3 : ∀ᶠ N : ℕ in atTop, 4 * (2 * p : ℝ) ^ (2 * p) ≤ (N : ℝ) - 1 :=
    hNm.eventually_ge_atTop _
  filter_upwards [e1, e2, e3] with N h1 h2 h3
  exact key_bound p hp N (d N) h1 (by exact_mod_cast h2) h3

end PartA
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
/-! ## Assembly -/

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartA
lemma exists_p_small (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    ∃ p : ℕ, 1 ≤ p ∧ r ^ p * ((2 * p + 1) * (p + 1)) ≤ 1 / 4 := by
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (r := r) (by rw [abs_of_nonneg hr0]; exact hr)
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 * r ^ n < 1 / 24 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨p, hp1, hp2⟩ := ((eventually_ge_atTop 1).and hev).exists
  refine ⟨p, hp1, ?_⟩
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hrp : 0 ≤ r ^ p := pow_nonneg hr0 _
  have : ((2 * p + 1) * (p + 1) : ℝ) ≤ 6 * (p : ℝ) ^ 2 := by nlinarith
  calc r ^ p * ((2 * p + 1) * (p + 1)) ≤ r ^ p * (6 * (p : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left this hrp
    _ = 6 * ((p : ℝ) ^ 2 * r ^ p) := by ring
    _ ≤ 6 * (1 / 24) := by linarith
    _ = 1 / 4 := by norm_num

/-- Bernoulli: `(2d − 1)^p ≤ 2 (2(d − p))^p` once `d ≥ 4p² + 1`. -/
lemma pow_le_two_mul_pow (p d : ℕ) (hd : 4 * p ^ 2 + 1 ≤ d) :
    (2 * (d : ℝ) - 1) ^ p ≤ 2 * (2 * ((d : ℝ) - p)) ^ p := by
  have hd' : (4 * (p : ℝ) ^ 2 + 1) ≤ d := by exact_mod_cast hd
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  set x : ℝ := 2 * (d : ℝ) - 1 with hx
  have hxpos : 0 < x := by nlinarith
  set a : ℝ := -(2 * (p : ℝ) - 1) / x with ha
  have hxa : x * (1 + a) = 2 * ((d : ℝ) - p) := by
    rw [ha, mul_add, mul_div_cancel₀ _ hxpos.ne']; ring
  have hpa : (p : ℝ) * (2 * p - 1) ≤ x / 2 := by nlinarith
  have hapos : -2 ≤ a := by
    rw [ha, le_div_iff₀ hxpos]; nlinarith
  have hB := one_add_mul_le_pow hapos p
  have h12 : (1 : ℝ) / 2 ≤ 1 + p * a := by
    have : (p : ℝ) * a = -((p : ℝ) * (2 * p - 1)) / x := by rw [ha]; ring
    rw [this]
    have : (p : ℝ) * (2 * p - 1) / x ≤ 1 / 2 := by
      rw [div_le_iff₀ hxpos]; linarith
    rw [neg_div]; linarith
  rw [← hxa, mul_pow]
  have hxp : 0 ≤ x ^ p := pow_nonneg hxpos.le _
  nlinarith

/-- Part A. Choosing `p`: for every `δ > 0` there are `p ≥ 1` and `d₀` such that for `d ≥ d₀`,
`((1 − δ)·2√(2d − 1))^{2p} ≤ retCount d (2p) / 2`. -/
theorem exists_p_retCount (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ p : ℕ, 1 ≤ p ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
      ((1 - δ) * (2 * Real.sqrt (2 * d - 1))) ^ (2 * p) ≤ (retCount d (2 * p) : ℝ) / 2 := by
  set r : ℝ := (1 - δ) ^ 2 with hr
  have hr0 : 0 ≤ r := sq_nonneg _
  have hr1 : r < 1 := by rw [hr]; nlinarith
  obtain ⟨p, hp1, hpr⟩ := exists_p_small r hr0 hr1
  refine ⟨p, hp1, 4 * p ^ 2 + 1, fun d hd => ?_⟩
  have hdp : p ≤ d := by nlinarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hx0 : (0 : ℝ) ≤ 2 * d - 1 := by linarith
  have hlhs : ((1 - δ) * (2 * Real.sqrt (2 * d - 1))) ^ (2 * p) =
      r ^ p * 4 ^ p * (2 * (d : ℝ) - 1) ^ p := by
    have hs : (2 * Real.sqrt (2 * d - 1)) ^ 2 = 4 * (2 * (d : ℝ) - 1) := by
      rw [mul_pow, Real.sq_sqrt hx0]; norm_num
    rw [pow_mul, mul_pow, hs, ← hr, mul_pow, mul_pow (4 : ℝ), mul_assoc]
  rw [hlhs]
  have hK := retCount_ge d p hdp
  have hcat := four_pow_le_catalan p
  have hB := pow_le_two_mul_pow p d hd
  set cat : ℝ := (catalan p : ℝ)
  have hcat0 : 0 ≤ cat := Nat.cast_nonneg _
  have hX0 : 0 ≤ (2 * (d : ℝ) - 1) ^ p := pow_nonneg hx0 _
  have hrp : 0 ≤ r ^ p := pow_nonneg hr0 _
  have h1 : r ^ p * 4 ^ p * (2 * (d : ℝ) - 1) ^ p ≤
      r ^ p * ((2 * p + 1) * (p + 1)) * cat * (2 * (d : ℝ) - 1) ^ p := by
    have := mul_le_mul_of_nonneg_left hcat hrp
    have := mul_le_mul_of_nonneg_right this hX0
    linarith
  have h2 : r ^ p * ((2 * p + 1) * (p + 1)) * cat * (2 * (d : ℝ) - 1) ^ p ≤
      1 / 4 * cat * (2 * (d : ℝ) - 1) ^ p := by
    have := mul_le_mul_of_nonneg_right hpr (mul_nonneg hcat0 hX0)
    linarith
  have h3 : 1 / 4 * cat * (2 * (d : ℝ) - 1) ^ p ≤ cat * 2 ^ p * ((d : ℝ) - p) ^ p / 2 := by
    have := mul_le_mul_of_nonneg_left hB hcat0
    rw [mul_pow] at this
    linarith
  linarith

end PartA
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartA
theorem tendsto_prob_norm_adjPerp_ge_highDegree_dev (d : ℕ → ℕ)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ) / Real.log N ^ 4) atTop atTop) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin (d N) → Equiv.Perm (Fin N) =>
      (1 - δ) * (2 * Real.sqrt (2 * d N - 1)) ≤ ‖adjPerp σ‖)) atTop (𝓝 1) := by
  rcases le_or_gt 1 δ with h1 | h1
  · have : ∀ N : ℕ, uniformProb (fun σ : Fin (d N) → Equiv.Perm (Fin N) =>
        (1 - δ) * (2 * Real.sqrt (2 * d N - 1)) ≤ ‖adjPerp σ‖) = 1 := by
      intro N
      apply prob_of_forall
      intro σ
      have : (1 - δ) * (2 * Real.sqrt (2 * d N - 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      exact this.trans (norm_nonneg _)
    simp only [this]
    exact tendsto_const_nhds
  -- `d N → ∞`
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := by
    have := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop 1
  have hdinf : Tendsto (fun N => (d N : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hd
    filter_upwards [hlog] with N hN
    have h4 : 1 ≤ Real.log N ^ 4 := one_le_pow₀ hN
    exact div_le_self (Nat.cast_nonneg _) h4
  obtain ⟨p, hp1, d₀, hd₀⟩ := exists_p_retCount δ hδ h1
  have hG := tendsto_prob_trMoment_ge d hdinf p hp1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hG tendsto_const_nhds ?_
    (Eventually.of_forall fun N => prob_le_one _)
  have e1 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have e2 : ∀ᶠ N : ℕ in atTop, (d₀ : ℝ) ≤ d N := hdinf.eventually_ge_atTop _
  filter_upwards [e1, e2] with N hN hdN
  apply prob_mono
  intro σ hσ
  have hdN' : d₀ ≤ d N := by exact_mod_cast hdN
  have hle := trMoment_le (by omega : 1 ≤ N) σ p
  have hn : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hK : (retCount (d N) (2 * p) : ℝ) / 2 ≤ ‖adjPerp σ‖ ^ (2 * p) := by
    have : ((N : ℝ) - 1) * ((retCount (d N) (2 * p) : ℝ) / 2) ≤
        ((N : ℝ) - 1) * ‖adjPerp σ‖ ^ (2 * p) := by
      calc _ = ((N : ℝ) - 1) * retCount (d N) (2 * p) / 2 := by ring
        _ ≤ _ := hσ.trans hle
    exact le_of_mul_le_mul_left this hn
  exact le_of_pow_le_pow_left₀ (by omega) (norm_nonneg _) ((hd₀ (d N) hdN').trans hK)

end PartA
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
alias tendsto_prob_norm_adjPerp_ge_highDegree_dev := StrongConv.HighDeg.PartA.tendsto_prob_norm_adjPerp_ge_highDegree_dev

end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartE
open Equiv

end PartE
end StrongConv.HighDeg
end
end

section
noncomputable section
namespace StrongConv.HighDeg
open Filter Topology
namespace PartW

end PartW
end StrongConv.HighDeg
end
end

open Filter Topology in
theorem solution (d : ℕ → ℕ)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ) / Real.log N ^ 4) atTop atTop) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => StrongConv.uniformProb (fun σ : Fin (d N) → Equiv.Perm (Fin N) =>
      (1 - δ) * (2 * Real.sqrt (2 * d N - 1)) ≤ ‖StrongConv.adjPerp σ‖)) atTop (𝓝 1) :=
  StrongConv.HighDeg.tendsto_prob_norm_adjPerp_ge_highDegree_dev d hd δ hδ

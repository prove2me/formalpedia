-- Prove2me | solution 1 for StrongConv.tendsto_prob_abs_norm_schreierAdjPerp_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:59:02.764208+00:00
-- url     : https://prove2.me/submissions/176c50a7-950f-4bc9-baac-1258087c13ff

import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG2
import Theorems.Thm_StrongConv_exists_stableRep_noTrivialSummand_schreierAdjPerp_eq
import Theorems.Thm_StrongConv_prob_norm_eval_stableRep_ge_le
import Theorems.Thm_StrongConv_tendsto_prob_norm_eval_stableRep_ge_sub
import Theorems.Thm_StrongConv_norm_adjFree
import Mathlib

section
section
open Polynomial Filter Topology

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace StrongConv

def T34_P (d : ℕ) : NCPoly 1 d :=
  ∑ l : Fin d ⊕ Fin d, Finsupp.single (FreeMonoid.of l) (1 : Matrix (Fin 1) (Fin 1) ℂ)

lemma T34_tensorOp_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (T : H →L[ℂ] H) : tensorOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  ext x i
  simp [tensorOp]

lemma T34_tensorOp_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  ext x i
  simp [tensorOp, add_smul, Finset.sum_add_distrib]

lemma T34_sum_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) (s : Finset (Fin d ⊕ Fin d)) :
    (∑ l ∈ s, Finsupp.single (FreeMonoid.of l) (1 : Matrix (Fin 1) (Fin 1) ℂ)).sum
      (fun w A => tensorOp A (wordOp u w)) =
      ∑ l ∈ s, tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (letterOp u l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih =>
    rw [Finset.sum_insert hl, Finset.sum_insert hl,
      Finsupp.sum_add_index' (fun w => T34_tensorOp_zero _) (fun w A B => T34_tensorOp_add A B _), ih,
      Finsupp.sum_single_index (T34_tensorOp_zero _)]
    simp [wordOp]

lemma T34_eval_P {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    (T34_P d).eval u = ∑ l : Fin d ⊕ Fin d, tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) (letterOp u l) :=
  T34_sum_single d u Finset.univ

/-- the identification `PiLp 2 (Fin 1 → H) ≃ H` -/
def T34_E (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    PiLp 2 (fun _ : Fin 1 => H) ≃ₗᵢ[ℂ] H where
  toFun x := x 0
  invFun y := WithLp.toLp 2 (fun _ => y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    ext i
    have : i = 0 := Subsingleton.elim _ _
    subst this; rfl
  right_inv _ := rfl
  norm_map' x := by
    show ‖x 0‖ = ‖x‖
    rw [PiLp.norm_eq_of_L2]
    simp

lemma T34_tensorOp_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    tensorOp (1 : Matrix (Fin 1) (Fin 1) ℂ) T = (T34_E H).symm.conjStarAlgEquiv T := by
  ext x i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simp [tensorOp, T34_E]
  rfl

lemma T34_eval_P' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    (T34_P d).eval u = (T34_E H).symm.conjStarAlgEquiv (∑ i, (u i + star (u i))) := by
  rw [T34_eval_P]
  simp only [T34_tensorOp_one, ← map_sum, Fintype.sum_sum_type, letterOp, Finset.sum_add_distrib]


/-! ## Part A: facts about `P` -/

lemma T34_P_apply (d : ℕ) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    T34_P d w = if w.length = 1 then 1 else 0 := by
  classical
  unfold T34_P
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  by_cases hw : w.length = 1
  · obtain ⟨a, ha⟩ : ∃ a, w = FreeMonoid.of a := by
      have : w.toList.length = 1 := hw
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp this
      exact ⟨a, by apply FreeMonoid.toList.injective; simpa using ha⟩
    subst ha
    rw [if_pos hw, Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)]
    · simp
    · rw [if_neg]
      intro h
      exact hb (FreeMonoid.of_injective h)
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro l _
    rw [if_neg]
    rintro rfl
    exact hw (by simp)

lemma T34_wordStar_length (d : ℕ) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    (NCPoly.wordStar w).length = w.length := by
  simp [NCPoly.wordStar, FreeMonoid.length]

lemma T34_P_selfAdjoint (d : ℕ) : (T34_P d).IsSelfAdjoint := by
  intro w
  rw [T34_P_apply, T34_P_apply, T34_wordStar_length]
  split_ifs <;> simp

lemma T34_P_degree (d : ℕ) : (T34_P d).degree ≤ 1 := by
  unfold NCPoly.degree
  apply Finset.sup_le
  intro w hw
  rw [Finsupp.mem_support_iff, T34_P_apply] at hw
  by_contra hc
  exact hw (if_neg (by omega))

lemma T34_norm_unitary_le {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) with hs | hs
  · rw [Subsingleton.elim (Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ)) 0]
    simp
  · have hU := Unitary.mem_iff.mp U.2
    have hmem : Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ) ∈
        unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
      rw [Unitary.mem_iff]
      constructor
      · rw [← map_star, ← map_mul, hU.1, map_one]
      · rw [← map_star, ← map_mul, hU.2, map_one]
    exact (CStarRing.norm_of_mem_unitary hmem).le

lemma T34_norm_eval_le (d : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (hu : ∀ i, ‖u i‖ ≤ 1) :
    ‖(T34_P d).eval u‖ ≤ 2 * d := by
  rw [T34_eval_P', StarAlgEquiv.norm_map]
  calc ‖∑ i, (u i + star (u i))‖ ≤ ∑ i, ‖u i + star (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        calc ‖u i + star (u i)‖ ≤ ‖u i‖ + ‖star (u i)‖ := norm_add_le _ _
          _ ≤ 2 := by rw [norm_star]; linarith [hu i]
    _ = 2 * d := by simp [mul_comm]

lemma T34_fullNorm (d : ℕ) : (T34_P d).fullNorm = 2 * d := by
  unfold NCPoly.fullNorm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨1, fun _ => 1, ?_⟩
    rw [T34_eval_P', StarAlgEquiv.norm_map]
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ)
        (((1 : Matrix.unitaryGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ)) =
        (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) := by
      simp
    simp only [h1, star_one]
    rw [← two_smul ℂ (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, norm_smul, norm_one]
    simp
    ring
  · rintro x ⟨n, U, rfl⟩
    exact T34_norm_eval_le d _ fun i => T34_norm_unitary_le (U i)



lemma T34_norm_eval {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : ℕ) (u : Fin d → H →L[ℂ] H) :
    ‖(T34_P d).eval u‖ = ‖∑ i, (u i + star (u i))‖ := by
  rw [T34_eval_P', StarAlgEquiv.norm_map]

lemma T34_norm_sLimit (d : ℕ) : ‖(T34_P d).eval (sLimit d)‖ = ‖adjFree d‖ :=
  T34_norm_eval d (sLimit d)

end StrongConv

end
end
end

section
section
open Filter Topology

namespace StrongConv
namespace W2Sec3

theorem uniformProb_le_add {X : Type*} [Fintype X] (L U E : X → Prop)
    (h : ∀ x, L x → U x ∨ E x) : uniformProb L ≤ uniformProb U + uniformProb E := by
  classical
  unfold uniformProb
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have : (Finset.univ.filter L) ⊆ (Finset.univ.filter U) ∪ (Finset.univ.filter E) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    exact h x hx
  have := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
  exact_mod_cast this

theorem uniformProb_le_one {X : Type*} [Fintype X] (E : X → Prop) : uniformProb E ≤ 1 := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

theorem uniformProb_nonneg {X : Type*} [Fintype X] (E : X → Prop) : 0 ≤ uniformProb E := by
  classical
  unfold uniformProb; positivity

theorem norm_eq_of_intertwine {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace A] [CompleteSpace B]
    (U : A ≃ₗᵢ[ℂ] B) (S : A →L[ℂ] A) (T : B →L[ℂ] B) (h : ∀ x, U (S x) = T (U x)) :
    ‖S‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    calc ‖S x‖ = ‖U (S x)‖ := (U.norm_map _).symm
      _ = ‖T (U x)‖ := by rw [h]
      _ ≤ ‖T‖ * ‖U x‖ := T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [U.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    obtain ⟨x, rfl⟩ := U.surjective y
    calc ‖T (U x)‖ = ‖U (S x)‖ := by rw [h]
      _ = ‖S x‖ := U.norm_map _
      _ ≤ ‖S‖ * ‖x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖U x‖ := by rw [U.norm_map]

theorem tuple_dim_pos (k N : ℕ) (hk : 1 ≤ k) (hN : k + 1 ≤ N) :
    0 < Module.finrank ℂ (TupleOnesPerp k N) := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (ℂ ∙ tupleOnes k N)
  have h2 : Module.finrank ℂ (ℂ ∙ tupleOnes k N) ≤ 1 := by
    simpa using finrank_span_le_card ({tupleOnes k N} : Set _)
  have h3 : 2 ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin k ↪ Fin N)) := by
    rw [finrank_euclideanSpace]
    have : 1 < Fintype.card (Fin k ↪ Fin N) := by
      rw [Fintype.one_lt_card_iff]
      refine ⟨⟨fun i => ⟨i, by omega⟩, fun i j h => by simpa [Fin.ext_iff] using h⟩,
        ⟨fun i => ⟨i + 1, by omega⟩, fun i j h => by simpa [Fin.ext_iff] using h⟩, ?_⟩
      intro h
      have := congrArg (fun e : Fin k ↪ Fin N => (e ⟨0, by omega⟩ : ℕ)) h
      simp at this
    omega
  show 0 < Module.finrank ℂ ↥(ℂ ∙ tupleOnes k N)ᗮ
  omega


theorem tendsto_dev (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      |‖schreierAdjPerp k σ‖ - 2 * Real.sqrt (2 * d - 1)| ≤ δ)) atTop (𝓝 1) := by
  obtain ⟨π, hπ, hU⟩ := exists_stableRep_noTrivialSummand_schreierAdjPerp_eq k
  set P := T34_P d with hP
  set a := 2 * Real.sqrt (2 * d - 1) with ha
  have hF := norm_adjFree d (by omega)
  have hsL : ‖P.eval (sLimit d)‖ = a := by rw [T34_norm_sLimit, hF]
  have hfn := T34_fullNorm d
  -- the stable representation with a larger N₀
  set N₁ := max π.N₀ (k + 1) with hN₁
  let π' : StableRep :=
    { π with
      N₀ := N₁
      trace_eq := fun N hN σ => π.trace_eq N (le_trans (le_max_left _ _) hN) σ }
  have hπ' : π'.NoTrivialSummand := fun N hN v hv =>
    hπ N (le_trans (le_max_left _ _) hN) v hv
  have hdim : ∀ N, π'.N₀ ≤ N → 0 < π'.dim N := by
    intro N hN
    obtain ⟨U, -⟩ := hU N (le_trans (le_max_left _ _) hN)
    have h1 := tuple_dim_pos k N hk (le_trans (le_max_right _ _) hN)
    have h2 := U.toLinearEquiv.finrank_eq
    rw [finrank_euclideanSpace, Fintype.card_fin] at h2
    show 0 < π.dim N
    omega
  -- norms agree
  have hnorm : ∀ N, N₁ ≤ N → ∀ σ : Fin d → Equiv.Perm (Fin N),
      ‖schreierAdjPerp k σ‖ = ‖P.eval (π.model σ)‖ := by
    intro N hN σ
    obtain ⟨U, hUσ⟩ := hU N (le_trans (le_max_left _ _) hN)
    rw [T34_norm_eval]
    exact norm_eq_of_intertwine U.symm.symm _ _ (hUσ d σ)
  -- upper bound
  have hgap : 0 < 2 * (d : ℝ) - a := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : Real.sqrt (2 * d - 1) < d := by
      rw [Real.sqrt_lt' (by linarith)]; nlinarith
    rw [ha]; linarith
  set δ₁ := min δ ((2 * (d : ℝ) - a) / 2) with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min hδ (by linarith)
  have hδ₁lt : δ₁ < P.fullNorm - ‖P.eval (sLimit d)‖ := by
    rw [hfn, hsL]; have := min_le_right δ ((2 * (d : ℝ) - a) / 2); linarith
  obtain ⟨C, hC⟩ := prob_norm_eval_stableRep_ge_le π' hπ'
  set c := C * 1 * ((P.fullNorm * ((1:ℕ):ℝ) * Real.log d / δ₁) ^ (4 * (π'.alpha + 1)) *
      Real.log (Real.exp 1 * P.fullNorm / δ₁)) with hc
  have hup : Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      a + δ₁ ≤ ‖schreierAdjPerp k σ‖)) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun N => uniformProb_nonneg _) _
      (tendsto_const_div_atTop_nhds_zero_nat c)
    filter_upwards [eventually_ge_atTop N₁] with N hN
    have h := hC 1 d 1 hd P (T34_P_selfAdjoint d) (by simpa using T34_P_degree d) δ₁ hδ₁pos hδ₁lt N hN
    rw [hsL] at h
    have e : (fun σ : Fin d → Equiv.Perm (Fin N) => a + δ₁ ≤ ‖schreierAdjPerp k σ‖) =
        fun σ => a + δ₁ ≤ ‖P.eval (π'.model σ)‖ := by
      funext σ; rw [hnorm N hN σ]; rfl
    rw [e]
    refine h.trans_eq ?_
    rw [hc]; ring
  have hlow := tendsto_prob_norm_eval_stableRep_ge_sub π' hπ' hdim P δ hδ
  have hlow' : Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      a - δ ≤ ‖schreierAdjPerp k σ‖)) atTop (𝓝 1) := by
    refine hlow.congr' ?_
    filter_upwards [eventually_ge_atTop N₁] with N hN
    congr 1
    funext σ
    rw [hsL, hnorm N hN σ]
    rfl
  have hdiff := hlow'.sub hup
  rw [sub_zero] at hdiff
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hdiff tendsto_const_nhds
  · filter_upwards with N
    have := uniformProb_le_add (fun σ : Fin d → Equiv.Perm (Fin N) => a - δ ≤ ‖schreierAdjPerp k σ‖)
      (fun σ => a + δ₁ ≤ ‖schreierAdjPerp k σ‖)
      (fun σ => |‖schreierAdjPerp k σ‖ - a| ≤ δ) (fun σ hσ => by
        by_cases hh : a + δ₁ ≤ ‖schreierAdjPerp k σ‖
        · exact Or.inl hh
        · right
          rw [abs_le]
          have : ‖schreierAdjPerp k σ‖ < a + δ₁ := not_le.mp hh
          have : δ₁ ≤ δ := min_le_left _ _
          constructor <;> linarith)
    linarith
  · filter_upwards with N
    exact uniformProb_le_one _

end W2Sec3

theorem tendsto_prob_abs_norm_schreierAdjPerp_sub_le_dev (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (δ : ℝ)
    (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      |‖schreierAdjPerp k σ‖ - 2 * Real.sqrt (2 * d - 1)| ≤ δ)) atTop (𝓝 1) :=
  W2Sec3.tendsto_dev d k hd hk δ hδ

end StrongConv

end
end

section
open StrongConv

open Filter Topology


theorem solution (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (δ : ℝ)
    (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      |‖schreierAdjPerp k σ‖ - 2 * Real.sqrt (2 * d - 1)| ≤ δ)) atTop (𝓝 1) := by
  exact StrongConv.tendsto_prob_abs_norm_schreierAdjPerp_sub_le_dev d k hd hk δ hδ

end

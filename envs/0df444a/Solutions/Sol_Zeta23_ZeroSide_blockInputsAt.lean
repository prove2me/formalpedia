-- Prove2me | solution 1 for Zeta23.ZeroSide.blockInputsAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:06:07.192932+00:00
-- url     : https://prove2.me/submissions/b4e5753d-93a4-40d1-843e-2ee73de2cb79

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_ZeroSide
import Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_posIndex_blockA_le
import Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_posIndex_blockQ_le
import Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_rtrace_blockP_le
import Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_sum_split
import Theorems.Thm_Zeta23_ZeroSide_card_offLine_eq_mk
import Theorems.Thm_Zeta23_ZeroSide_posIndex_smul_pos
import Theorems.Thm_Zeta23_ZeroSide_sum_filter_coe
import Theorems.Thm_Zeta23_ZeroSide_sum_normSq_v_le

-- from Zeta23.ZeroSide
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZeroSide.lean — paper §4 "The zero side: signature and rank", Block structure + prop:block.
Builds on the §3 formalization (Zeta23.LinAlg, namespace RHLinalg): posIndex, posIndex_add_le
(subadditivity, the corollary of lem:inertia), Sylvester's subspace characterization,
posIndex_eq_rank_of_posSemidef.

Reference text: the paper, labels [eq:AE], [eq:Ncount], [eq:hatunits], [prop:block].

Design: this file is ζ-free. Section 1 is generic Hermitian-matrix
lemmas missing from Mathlib/RHLinalg. Section 2 proves prop:block for an ABSTRACT finite
zero configuration `ZeroBlockData` (distinct points z with explicit multiplicities m z ≥ 1,
the involution σ = (ρ ↦ 1 − conj ρ) with m ∘ σ = m, and evaluation vectors v z = (φ̂(γ_z − τ_k))_k with
v (σ z) = conj ∘ v z). Section 3 instantiates from Defs.lean's ZeroConfig, φ̂, τ_k, a, L and
lem:poisson.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide

/-! ## Section 1. Generic lemmas on rank and positive index -/

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `rank (A + B) ≤ rank A + rank B` for matrices (Mathlib has this only for linear maps). -/
lemma rank_add_le (A B : Matrix n n 𝕜) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro _ ⟨x, rfl⟩
  simp only [mulVecLin_apply, add_mulVec]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

omit [DecidableEq n] in
/-- Rank of a finite sum is at most the sum of given rank bounds. -/
lemma rank_sum_le {α : Type*} (s : Finset α) (f : α → Matrix n n 𝕜) (b : α → ℕ)
    (h : ∀ a ∈ s, (f a).rank ≤ b a) : (∑ a ∈ s, f a).rank ≤ ∑ a ∈ s, b a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (rank_add_le _ _).trans
      (Nat.add_le_add (h a (mem_insert_self a s)) (ih fun x hx => h x (mem_insert_of_mem hx)))

omit [DecidableEq n] in
/-- A scalar multiple of a rank-one matrix `w vᵀ` has rank at most one. -/
lemma rank_smul_vecMulVec_le (c : 𝕜) (w v : n → 𝕜) :
    (c • vecMulVec w v).rank ≤ 1 := by
  rw [← smul_vecMulVec]
  exact rank_vecMulVec_le _ _







/-- Rank is invariant under multiplication by a nonzero scalar. -/
lemma rank_smul_of_ne_zero (A : Matrix n n 𝕜) {c : 𝕜} (hc : c ≠ 0) : (c • A).rank = A.rank := by
  apply le_antisymm
  · simpa using rank_mul_le_right (c • (1 : Matrix n n 𝕜)) A
  · calc A.rank = ((c⁻¹ • (1 : Matrix n n 𝕜)) * (c • A)).rank := by
          rw [Matrix.smul_mul, one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ ≤ (c • A).rank := rank_mul_le_right _ _

end Generic

/-! ## Section 2. The abstract block structure (paper §4: [eq:AE], Block structure, [eq:Ncount], [prop:block])

Paper §4, Block structure, verbatim: "Let 𝒵(I') be the set of distinct zeros with γ ∈ I'. Classify its
points as follows: 𝒮₁: β = ½ and m_ρ = 1 (simple zeros on the line); s₁ := #𝒮₁; 𝒮₂: β = ½ and
m_ρ ≥ 2; s₂ := #𝒮₂; 𝒫: unordered pairs {ρ, 1−ρ̄} with β ≠ ½ (both members lie in 𝒵(I'), they are
distinct points, and m_{1−ρ̄} = m_ρ); p := #𝒫. Thus #𝒵(I') = s₁+s₂+2p and, counting with
multiplicity, N(I') = Σ_{𝒮₁} 1 + Σ_{𝒮₂} m_ρ + Σ_{𝒫} 2m_ρ ≥ s₁+2s₂+2p. [eq:Ncount]
Write N_on(I') := Σ_{ρ∈𝒮₁∪𝒮₂} m_ρ, so that also N(I') ≥ N_on(I') + 2p."

We encode 𝒵(I') as a finite index type ι, the grid {0,…,d−1} as a finite type d, and carry:
multiplicities m (≥ 1, explicit — zeros are DISTINCT points), the involution σ = (ρ ↦ 1−ρ̄)
restricted to 𝒵(I') (it preserves the ordinate, hence 𝒵(I')), and the evaluation vectors
u_ρ = (φ̂(γ_ρ − τ_k))_{k<d} ∈ ℂ^d with u_{1−ρ̄} = conj u_ρ (from γ_{1−ρ̄} = conj γ_ρ, τ_k ∈ ℝ, and
conj φ̂(z̄) = φ̂(z) [subsec:family after eq:fk]). On-line ⟺ β = ½ ⟺ σ ρ = ρ.
-/

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]


namespace ZeroBlockData

variable (D : ZeroBlockData ι d)









variable {D}



variable (D) (P : D.PairReps)



/-- #𝒵(I') = #(𝒮₁∪𝒮₂) + 2p. -/
lemma card_eq_onLine_add : Fintype.card ι = #D.onLine + 2 * P.p := by
  have := D.sum_split P (fun _ => (1 : ℕ))
  simpa [sum_const, smul_eq_mul, PairReps.p, Nat.mul_comm] using this

lemma onLine_eq_S₁_union_S₂ : D.onLine = D.S₁ ∪ D.S₂ := by
  ext z
  simp only [onLine, S₁, S₂, mem_filter, mem_univ, true_and, mem_union]
  constructor
  · intro h
    rcases Nat.lt_or_ge (D.m z) 2 with h2 | h2
    · left; exact ⟨h, le_antisymm (Nat.lt_succ_iff.mp h2) (D.one_le_m z)⟩
    · right; exact ⟨h, h2⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

lemma disjoint_S₁_S₂ : Disjoint D.S₁ D.S₂ := by
  rw [disjoint_iff_ne]; rintro a ha _ hb rfl
  simp only [S₁, S₂, mem_filter, mem_univ, true_and] at ha hb
  omega

/-- #(𝒮₁ ∪ 𝒮₂) = s₁ + s₂. -/
lemma card_onLine : #D.onLine = D.s₁ + D.s₂ := by
  rw [onLine_eq_S₁_union_S₂, card_union_of_disjoint D.disjoint_S₁_S₂]; rfl

/-- "#𝒵(I') = s₁ + s₂ + 2p" [§4 Block structure]. -/
theorem card_eq : Fintype.card ι = D.s₁ + D.s₂ + 2 * P.p := by
  rw [D.card_eq_onLine_add P, card_onLine]

/-- N_on(I') ≥ s₁ + 2 s₂ (since m_ρ = 1 on 𝒮₁ and m_ρ ≥ 2 on 𝒮₂). -/
lemma s₁_add_two_s₂_le_Non : D.s₁ + 2 * D.s₂ ≤ D.Non := by
  unfold Non s₁ s₂
  rw [onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂]
  apply Nat.add_le_add
  · rw [card_eq_sum_ones]
    exact sum_le_sum fun z hz => D.one_le_m z
  · rw [card_eq_sum_ones, mul_sum]
    exact sum_le_sum fun z hz => by
      simp only [S₂, mem_filter, mem_univ, true_and] at hz; simpa using hz.2

/-- "N(I') ≥ N_on(I') + 2p" [§4, after eq:Ncount]. -/
theorem Non_add_two_p_le_Ncount : D.Non + 2 * P.p ≤ D.Ncount := by
  unfold Ncount Non PairReps.p
  rw [D.sum_split P, card_eq_sum_ones, mul_sum]
  apply Nat.add_le_add_left
  exact sum_le_sum fun z _ => by
    have := D.one_le_m z; have := D.one_le_m (D.σ z); omega

/-- [eq:Ncount]: "N(I') = Σ_{𝒮₁} 1 + Σ_{𝒮₂} m_ρ + Σ_{𝒫} 2m_ρ ≥ s₁ + 2s₂ + 2p". -/
theorem s₁_add_two_s₂_add_two_p_le_Ncount : D.s₁ + 2 * D.s₂ + 2 * P.p ≤ D.Ncount :=
  (Nat.add_le_add_right D.s₁_add_two_s₂_le_Non _).trans (D.Non_add_two_p_le_Ncount P)

/-! ### The matrix A [eq:AE] and its decomposition -/


lemma blockA_apply (k l : d) : D.blockA k l = ∑ z, (D.m z : ℂ) * (D.v z k * D.v z l) := by
  simp [blockA, Matrix.sum_apply, vecMulVec_apply]














lemma rank_onPart_le : D.onPart.rank ≤ #D.onLine := by
  unfold onPart
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp


omit [DecidableEq ι] in
/-- "A is a sum of #𝒵(I') matrices of rank one" ⟹ rank A ≤ #𝒵(I') [prop:block (i)]. -/
theorem rank_blockA_le : D.blockA.rank ≤ Fintype.card ι := by
  unfold blockA
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp

lemma posIndex_congr {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    posIndex hA = posIndex hB := by
  subst h; rfl


/-- prop:block (i) for any positive multiple r•A (Ã = A/L: "Dividing by L > 0 changes nothing"). -/
theorem posIndex_smul_blockA_le {r : ℝ} (hr : 0 < r) (h : ((r : ℂ) • D.blockA).IsHermitian) :
    posIndex h ≤ D.s₁ + D.s₂ + P.p := by
  have key : posIndex h = posIndex D.blockA_isHermitian := posIndex_smul_pos D.blockA_isHermitian hr h
  exact key ▸ D.posIndex_blockA_le P

/-- prop:block (i), rank, for any nonzero multiple: "rank(Ã) ≤ s₁ + s₂ + 2p = #𝒵(I')". -/
theorem rank_smul_blockA_le {r : ℂ} (hr : r ≠ 0) :
    (r • D.blockA).rank ≤ D.s₁ + D.s₂ + 2 * P.p := by
  rw [rank_smul_of_ne_zero _ hr, ← D.card_eq P]; exact D.rank_blockA_le

/-! ### prop:block (ii): Â = P + Q in the units [eq:hatunits] -/



/-- Â = P + Q where Â := A/(aL²) [eq:hatunits] (here: c⁻¹ • A with c = aL²). -/
theorem blockP_add_blockQ (c : ℝ) : D.blockP c + D.blockQ c = ((c⁻¹ : ℝ) : ℂ) • D.blockA := by
  unfold blockP blockQ; rw [← smul_add, add_sub_cancel]


/-- "P is … positive semidefinite". -/
theorem blockP_posSemidef {c : ℝ} (hc : 0 < c) : (D.blockP c).PosSemidef :=
  D.onPart_posSemidef.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))


/-- "of rank ≤ s₁ + s₂". -/
theorem rank_blockP_le {c : ℝ} (hc : 0 < c) : (D.blockP c).rank ≤ D.s₁ + D.s₂ := by
  unfold blockP
  rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne')), ← card_onLine]
  exact D.rank_onPart_le







end ZeroBlockData

end Block

/-! ## Section 3. Instantiation against Zeta23.Defs: 𝒵(I') ⊂ ZeroConfig, A = Z.Az P T  [eq:AE]

Here ι := 𝒵(I') = Z.ZIprime T (finite by ZeroConfig.finite_window), d := Fin (P.d T),
m := Z.mult, σ := reflect = (ρ ↦ 1 − conj ρ), v ρ k := φ̂(γ_ρ − τ_k) with γ_ρ = gammaOf ρ, τ_k = P.tau T k.
The analytic inputs are explicit hypotheses of this section (discharged elsewhere in the
repository from Zeta23.Taper / Zeta23.Poisson: Params.phiHat_conj, Params.phiHat_ofReal,
Params.hasSum_phiHatR_sq):
  hconj : ∀ z, φ̂(conj z) = conj φ̂(z)                       [subsec:family, after eq:fk]
  hreal : ∀ r : ℝ, φ̂(r) = φ̂_ℝ(r) (φ̂ real on ℝ)
  hPois : ∀ γ : ℝ, HasSum (k ↦ φ̂(γ − τ_k)²) (aL²)            [lem:poisson, "in particular"]
-/

section Inst

open Zeta23 Classical

variable (Z : ZeroConfig) (T : ℝ)




lemma coe_ZI : ((ZI Z T : Finset ℂ) : Set ℂ) = Z.ZIprime T := Set.Finite.coe_toFinset _









section mk
variable {d : Type*} [Fintype d] [DecidableEq d] (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z))

@[simp] lemma mkData_m (z : ZI Z T) : (mkData Z T v hv).m z = Z.mult z := rfl
@[simp] lemma mkData_v : (mkData Z T v hv).v = v := rfl



omit Z T in
lemma card_filter_coe (s : Finset ℂ) (p : ℂ → Prop) (q : s → Prop)
    (h : ∀ z : s, q z ↔ p z) : #{z : s | q z} = #(s.filter p) := by
  apply Finset.card_bij (fun (z : s) _ => (z : ℂ))
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact ⟨z.2, (h z).mp hz⟩
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb
    simp only [mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, by simp only [mem_filter, mem_univ, true_and]; exact (h _).mpr hb.2, rfl⟩


lemma S1_eq : Z.S1 T = ↑((ZI Z T).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)) := by
  ext ρ
  simp only [ZeroConfig.S1, ZeroConfig.onLine, ZeroConfig.simple, Set.mem_inter_iff,
    Set.mem_setOf_eq, Finset.coe_filter, mem_ZI]
  tauto

lemma S2_eq : Z.S2 T = ↑((ZI Z T).filter (fun ρ => ρ.re = 1 / 2 ∧ 2 ≤ Z.mult ρ)) := by
  ext ρ
  simp only [ZeroConfig.S2, ZeroConfig.onLine, Set.mem_inter_iff, Set.mem_setOf_eq,
    Finset.coe_filter, mem_ZI]
  tauto


lemma s1_eq_mk : Z.s1 T = (mkData Z T v hv).s₁ := by
  rw [ZeroConfig.s1, S1_eq, Set.ncard_coe_finset, ZeroBlockData.s₁, ZeroBlockData.S₁]
  convert (card_filter_coe (ZI Z T) (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)
    (fun z => (mkData Z T v hv).σ z = z ∧ (mkData Z T v hv).m z = 1)
    fun z => by beta_reduce; rw [mkData_σ_eq_iff]; rfl).symm using 2
  all_goals first | exact Finset.filter_congr_decidable _ _ _ | exact (Finset.filter_congr_decidable _ _ _).symm

lemma s2_eq_mk : Z.s2 T = (mkData Z T v hv).s₂ := by
  rw [ZeroConfig.s2, S2_eq, Set.ncard_coe_finset, ZeroBlockData.s₂, ZeroBlockData.S₂]
  convert (card_filter_coe (ZI Z T) (fun ρ => ρ.re = 1 / 2 ∧ 2 ≤ Z.mult ρ)
    (fun z => (mkData Z T v hv).σ z = z ∧ 2 ≤ (mkData Z T v hv).m z)
    fun z => by beta_reduce; rw [mkData_σ_eq_iff]; rfl).symm using 2
  all_goals first | exact Finset.filter_congr_decidable _ _ _ | exact (Finset.filter_congr_decidable _ _ _).symm


lemma p_eq_mk : Z.p T = (mkPairReps Z T v hv).p := by
  rw [ZeroConfig.p, card_offLine_eq_mk Z T v hv]; omega

lemma NIprime_eq_mk : Z.NIprime T = (mkData Z T v hv).Ncount := by
  rw [ZeroConfig.NIprime, ZeroConfig.N, ZeroBlockData.Ncount]
  change ∑ᶠ ρ ∈ Z.ZIprime T, Z.mult ρ = _
  rw [finsum_mem_eq_finite_toFinset_sum _ (ZIprime_finite Z T), ← Finset.sum_coe_sort]
  rfl

lemma NonIprime_eq_mk : Z.NonIprime T = (mkData Z T v hv).Non := by
  rw [ZeroConfig.NonIprime, ZeroConfig.N0, ZeroBlockData.Non, ZeroBlockData.onLine]
  have hset : Z.window (T - D0 T) (2 * T + D0 T) ∩ ZeroConfig.onLine
      = ↑((ZI Z T).filter fun ρ => ρ.re = 1 / 2) := by
    ext ρ
    simp only [ZeroConfig.onLine, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_filter, mem_ZI,
      ZeroConfig.ZIprime]
  rw [hset, finsum_mem_coe_finset]
  convert (sum_filter_coe (ZI Z T) (fun ρ => ρ.re = 1 / 2) (fun z => (mkData Z T v hv).σ z = z)
    (fun z => mkData_σ_eq_iff Z T v hv z) (fun ρ => Z.mult ρ)).symm using 2
  all_goals first | rfl | (ext; simp)

end mk


lemma zeroVec_reflect : ∀ z : ZI Z T, zeroVec Z T ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (zeroVec Z T z) :=
  fun _ => by ext; simp [zeroVec]

/-- **"#𝒵(I') = s₁ + s₂ + 2p"**  [§4 Block structure] (Defs' provisional p := #offLine/2). -/
theorem ncard_ZIprime_eq : (Z.ZIprime T).ncard = Z.s1 T + Z.s2 T + 2 * Z.p T := by
  have hv := zeroVec_reflect Z T
  rw [← coe_ZI, Set.ncard_coe_finset, s1_eq_mk Z T _ hv, s2_eq_mk Z T _ hv, p_eq_mk Z T _ hv,
    ← ZeroBlockData.card_eq _ (mkPairReps Z T _ hv), Fintype.card_coe]


/-- **[eq:Ncount]** "N(I') = Σ_{𝒮₁}1 + Σ_{𝒮₂}m_ρ + Σ_{𝒫}2m_ρ ≥ s₁ + 2s₂ + 2p". -/
theorem s1_add_two_s2_add_two_p_le_NIprime : Z.s1 T + 2 * Z.s2 T + 2 * Z.p T ≤ Z.NIprime T := by
  have hv := zeroVec_reflect Z T
  rw [s1_eq_mk Z T _ hv, s2_eq_mk Z T _ hv, p_eq_mk Z T _ hv, NIprime_eq_mk Z T _ hv]
  exact ZeroBlockData.s₁_add_two_s₂_add_two_p_le_Ncount _ _

/-- **"N(I') ≥ N_on(I') + 2p"** [§4, after eq:Ncount]. -/
theorem NonIprime_add_two_p_le_NIprime : Z.NonIprime T + 2 * Z.p T ≤ Z.NIprime T := by
  have hv := zeroVec_reflect Z T
  rw [p_eq_mk Z T _ hv, NIprime_eq_mk Z T _ hv, NonIprime_eq_mk Z T _ hv]
  exact ZeroBlockData.Non_add_two_p_le_Ncount _ _

/-! ### The matrix A = Z.Az P T and prop:block for Ã := P.tilde T A, Â := P.hat T A -/

variable (P : Params)



variable {Z T P}


variable (Z T P)


/-- **A = Σ_{ρ∈𝒵(I')} m_ρ u_ρ u_ρᵀ**: Defs' finsum matrix Z.Az P T [eq:AE] is the abstract blockA. -/
theorem Az_eq_blockA (hconj : PhiHatConj T P) : Z.Az P T = (blockData Z T P hconj).blockA := by
  ext k l
  rw [ZeroBlockData.blockA_apply]
  change ∑ᶠ ρ ∈ Z.ZIprime T, Z.Gsummand P T k l ρ = _
  rw [finsum_mem_eq_finite_toFinset_sum _ (ZIprime_finite Z T), ← Finset.sum_coe_sort]
  refine sum_congr rfl fun z _ => ?_
  simp only [ZeroConfig.Gsummand, blockData, mkData, evalVec]
  ring

/-- A is Hermitian (indeed real symmetric). -/
theorem Az_isHermitian (hconj : PhiHatConj T P) : (Z.Az P T).IsHermitian := by
  rw [Az_eq_blockA Z T P hconj]; exact ZeroBlockData.blockA_isHermitian _


omit Z in
lemma tilde_eq {n : Type*} (M : Matrix n n ℂ) : P.tilde T M = (((P.L T)⁻¹ : ℝ) : ℂ) • M := by
  unfold Params.tilde; push_cast; rfl

omit Z in
lemma hat_eq {n : Type*} (M : Matrix n n ℂ) :
    P.hat T M = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • M := by
  unfold Params.hat; push_cast; rfl

theorem tilde_Az_isHermitian (hconj : PhiHatConj T P) : (P.tilde T (Z.Az P T)).IsHermitian := by
  rw [tilde_eq]; exact ZeroBlockData.isHermitian_real_smul (Az_isHermitian Z T P hconj) _


/-- **prop:block (i)**: "n₊(Ã) ≤ s₁ + s₂ + p" (Ã := A/L; any Hermitian-ness witness h). -/
theorem posIndex_tilde_Az_le (hconj : PhiHatConj T P) (hL : 0 < P.L T)
    (h : (P.tilde T (Z.Az P T)).IsHermitian) :
    posIndex h ≤ Z.s1 T + Z.s2 T + Z.p T := by
  rw [s1_eq_mk Z T _ (evalVec_reflect hconj), s2_eq_mk Z T _ (evalVec_reflect hconj),
    p_eq_mk Z T _ (evalVec_reflect hconj)]
  have h' : ((((P.L T)⁻¹ : ℝ) : ℂ) • (blockData Z T P hconj).blockA).IsHermitian := by
    rw [← Az_eq_blockA, ← tilde_eq]; exact h
  rw [ZeroBlockData.posIndex_congr h h' (by rw [tilde_eq, Az_eq_blockA Z T P hconj])]
  exact ZeroBlockData.posIndex_smul_blockA_le _ _ (inv_pos.mpr hL) h'

/-- **prop:block (i)**: "rank(Ã) ≤ s₁ + s₂ + 2p = #𝒵(I')". -/
theorem rank_tilde_Az_le (hconj : PhiHatConj T P) (hL : 0 < P.L T) :
    (P.tilde T (Z.Az P T)).rank ≤ Z.s1 T + Z.s2 T + 2 * Z.p T := by
  rw [s1_eq_mk Z T _ (evalVec_reflect hconj), s2_eq_mk Z T _ (evalVec_reflect hconj),
    p_eq_mk Z T _ (evalVec_reflect hconj), tilde_eq, Az_eq_blockA Z T P hconj]
  exact ZeroBlockData.rank_smul_blockA_le _ _ (by exact_mod_cast (inv_ne_zero hL.ne'))



/-- **prop:block (ii)**: "Â = P + Q" with Â := A/(aL²) [eq:hatunits]. -/
theorem hat_Az_eq_hatP_add_hatQ (hconj : PhiHatConj T P) :
    P.hat T (Z.Az P T) = hatP Z T P hconj + hatQ Z T P hconj := by
  rw [hatP, hatQ, ZeroBlockData.blockP_add_blockQ, hat_eq, Az_eq_blockA Z T P hconj]

/-- **prop:block (ii)**: "P ⪰ 0". -/
theorem hatP_posSemidef (hconj : PhiHatConj T P) (hc : 0 < P.a T * P.L T ^ 2) :
    (hatP Z T P hconj).PosSemidef :=
  ZeroBlockData.blockP_posSemidef _ hc


/-- **prop:block (ii)**: "rank P ≤ s₁ + s₂". -/
theorem rank_hatP_le (hconj : PhiHatConj T P) (hc : 0 < P.a T * P.L T ^ 2) :
    (hatP Z T P hconj).rank ≤ Z.s1 T + Z.s2 T := by
  rw [s1_eq_mk Z T _ (evalVec_reflect hconj), s2_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.rank_blockP_le _ hc


/-- **prop:block (ii)**: "tr P ≤ N_on(I')" — "by Lemma [lem:poisson], tr P = (aL²)⁻¹ Σ m_ρ
Σ_{0≤k<d} φ̂(γ_ρ−τ_k)² ≤ (aL²)⁻¹ Σ m_ρ Σ_{k∈ℤ} φ̂(γ_ρ−τ_k)² = N_on(I')". -/
theorem rtrace_hatP_le (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2) :
    rtrace (hatP Z T P hconj) ≤ (Z.NonIprime T : ℝ) := by
  rw [NonIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.rtrace_blockP_le _ hc (sum_normSq_v_le Z T P hconj hreal hPois)

/-- **prop:block (ii)**: Q is Hermitian. -/
theorem hatQ_isHermitian (hconj : PhiHatConj T P) : (hatQ Z T P hconj).IsHermitian :=
  ZeroBlockData.blockQ_isHermitian _ _


/-- **prop:block (ii)**: "n₊(Q) ≤ p" (by lem:inertia), for any Hermitian-ness witness h. -/
theorem posIndex_hatQ_le (hconj : PhiHatConj T P) (hc : 0 < P.a T * P.L T ^ 2)
    (h : (hatQ Z T P hconj).IsHermitian) : posIndex h ≤ Z.p T := by
  rw [p_eq_mk Z T _ (evalVec_reflect hconj)]
  exact ZeroBlockData.posIndex_blockQ_le _ (mkPairReps Z T _ _) hc

end Inst

/-! ## Section 4. Packaging for Assembly: `Zeta23.Assembly.BlockInputs` -/

section Package

open Zeta23


/-! ### The export for Main.lean: eventually-in-T form with only the genuinely external inputs left

hconj / hreal are discharged here from Zeta23.GzGp.phiHat_conj / phiHat_ofReal
(φ real and even); 0 < L eventually since L = λ·log(T/2π) → ∞. What remains as hypotheses, both in
∀ᶠ form: positivity of a [eq:abdef] (Main has it from Taper: 1 − 2w/L ≤ b ≤ a) and lem:poisson
(Zeta23.Poisson: Params.hasSum_phiHatR_sq). Zeta23/ZeroSide/Final.lean discharges those two as well. -/



end Package

end Zeta23.ZeroSide
end
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23
open Zeta23.ZeroSide
open Zeta23

theorem solution (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hL : 0 < P.L T) (hc : 0 < P.a T * P.L T ^ 2) :
    Assembly.BlockInputs Z P T where
  hat := ⟨hatP Z T P hconj, hatQ Z T P hconj, Z.p T, hatP_posSemidef Z T P hconj hc,
    hatQ_isHermitian Z T P hconj, hat_Az_eq_hatP_add_hatQ Z T P hconj, rank_hatP_le Z T P hconj hc,
    rtrace_hatP_le Z T P hconj hreal hPois hc, posIndex_hatQ_le Z T P hconj hc _,
    by exact_mod_cast NonIprime_add_two_p_le_NIprime Z T⟩
  tilde := ⟨Z.p T, tilde_Az_isHermitian Z T P hconj, posIndex_tilde_Az_le Z T P hconj hL _,
    (ncard_ZIprime_eq Z T).symm ▸ rank_tilde_Az_le Z T P hconj hL,
    by exact_mod_cast s1_add_two_s2_add_two_p_le_NIprime Z T⟩

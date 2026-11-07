-- Prove2me | solution 1 for Puder.wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T09:44:01.422221+00:00
-- url     : https://prove2.me/submissions/bf1dc439-4791-4b65-b1f5-8c4e52d2a4ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Theorems.Thm_Puder_crit_finite_and_isBigO_uniformExp_card_fixedPoints
import Theorems.Thm_Puder_abs_asympCoeff_uniformExp_card_fixedPoints_le
import Theorems.Thm_Puder_isPrimitiveIn_of_isPrimitiveIn_top

section
open Filter Topology Asymptotics
namespace Puder.BP
/-- `E[#fix w(σ)]` over uniform `σ : Fin d → Perm (Fin N)`. -/
noncomputable abbrev expFix (d : ℕ) (w : FreeGroup (Fin d)) (N : ℕ) : ℝ :=
  StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    ((Finset.univ.filter fun x => FreeGroup.lift σ w x = x).card : ℝ))

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
/-! ### Part A1: `asympCoeff` -/
theorem asympCoeff_congr {F G : ℕ → ℝ} (h : F =ᶠ[atTop] G) (s : ℕ) :
    StrongConv.asympCoeff F s = StrongConv.asympCoeff G s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rw [StrongConv.asympCoeff.eq_1 F s, StrongConv.asympCoeff.eq_1 G s]
    have hsum : ∀ N : ℕ, ∑ i : Fin s, StrongConv.asympCoeff F i / (N : ℝ) ^ (i : ℕ) =
        ∑ i : Fin s, StrongConv.asympCoeff G i / (N : ℝ) ^ (i : ℕ) :=
      fun N => Finset.sum_congr rfl fun i _ => by rw [ih i i.isLt]
    simp_rw [hsum]
    unfold limUnder
    congr 1
    exact Filter.map_congr (h.mono fun N hN => by simp only [hN])

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
/-! ### Part A1: `asympCoeff` -/
alias asympCoeff_congr := Puder.BP.PartA.asympCoeff_congr

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
theorem asympCoeff_sub_const {F : ℕ → ℝ} {L : ℝ} (hF : Tendsto F atTop (𝓝 L)) (c : ℝ) {s : ℕ}
    (hs : 1 ≤ s) :
    StrongConv.asympCoeff (fun N => F N - c) s = StrongConv.asympCoeff F s := by
  have h0F : StrongConv.asympCoeff F 0 = L := by
    rw [StrongConv.asympCoeff.eq_1]
    simpa using hF.limUnder_eq
  have h0G : StrongConv.asympCoeff (fun N => F N - c) 0 = L - c := by
    rw [StrongConv.asympCoeff.eq_1]
    simpa using (hF.sub_const c).limUnder_eq
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    rw [StrongConv.asympCoeff.eq_1 (fun N => F N - c), StrongConv.asympCoeff.eq_1 F]
    congr 1
    funext N
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, div_one]
    rw [h0F, h0G]
    have hsum : ∑ i : Fin m, StrongConv.asympCoeff (fun N => F N - c) ((i : ℕ) + 1) /
          (N : ℝ) ^ ((i : ℕ) + 1) =
        ∑ i : Fin m, StrongConv.asympCoeff F ((i : ℕ) + 1) / (N : ℝ) ^ ((i : ℕ) + 1) :=
      Finset.sum_congr rfl fun i _ => by
        rw [ih _ (by omega) (by omega)]
    rw [hsum]
    ring

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
alias asympCoeff_sub_const := Puder.BP.PartA.asympCoeff_sub_const

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
/-- `(1/N)^j → 0` for `j ≥ 1`. -/
theorem tendsto_one_div_pow {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) ^ j) atTop (𝓝 0) := by
  have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow j
  rwa [zero_pow (by omega)] at this

theorem tendsto_pow_mul_aux {G : ℕ → ℝ} {K : ℝ} {k : ℕ}
    (h : (fun N : ℕ => G N - K / (N : ℝ) ^ k) =O[atTop] (fun N : ℕ => 1 / (N : ℝ) ^ (k + 1)))
    {s : ℕ} (hs : s ≤ k) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ s * G N) atTop (𝓝 (if s = k then K else 0)) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ s * (G N - K / (N : ℝ) ^ k)) atTop (𝓝 0) := by
    have hO := (isBigO_refl (fun N : ℕ => (N : ℝ) ^ s) atTop).mul h
    refine hO.trans_tendsto ?_
    refine (tendsto_one_div_pow (j := k + 1 - s) (by omega)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    generalize hj : k + 1 - s = j
    rw [show k + 1 = s + j by omega, pow_add, one_div_pow]
    field_simp
  have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ s * (K / (N : ℝ) ^ k)) atTop
      (𝓝 (if s = k then K else 0)) := by
    have h3 := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow (k - s)).const_mul K
    have h4 : K * (0 : ℝ) ^ (k - s) = if s = k then K else 0 := by
      split_ifs with hsk
      · subst hsk; simp
      · rw [zero_pow (by omega)]; simp
    rw [h4] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    generalize hj : k - s = j
    rw [show k = s + j by omega, pow_add, one_div_pow]
    field_simp
  have := h1.add h2
  rw [zero_add] at this
  refine this.congr fun N => ?_
  ring

theorem asympCoeff_of_isBigO {G : ℕ → ℝ} {K : ℝ} {k : ℕ}
    (h : (fun N : ℕ => G N - K / (N : ℝ) ^ k) =O[atTop] (fun N : ℕ => 1 / (N : ℝ) ^ (k + 1)))
    {s : ℕ} (hs : s ≤ k) :
    StrongConv.asympCoeff G s = if s = k then K else 0 := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rw [StrongConv.asympCoeff.eq_1]
    have hsum : ∀ N : ℕ, ∑ i : Fin s, StrongConv.asympCoeff G i / (N : ℝ) ^ (i : ℕ) = 0 := by
      intro N
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ih i i.isLt (by omega), if_neg (by omega), zero_div]
    simp_rw [hsum, sub_zero]
    exact (tendsto_pow_mul_aux h hs).limUnder_eq

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
alias asympCoeff_of_isBigO := Puder.BP.PartA.asympCoeff_of_isBigO

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
theorem asympCoeff_of_eventuallyEq_zero {G : ℕ → ℝ} (h : G =ᶠ[atTop] fun _ => 0) (s : ℕ) :
    StrongConv.asympCoeff G s = 0 := by
  rw [asympCoeff_congr h s]
  have hO : (fun N : ℕ => (fun _ : ℕ => (0 : ℝ)) N - 0 / (N : ℝ) ^ s) =O[atTop]
      (fun N : ℕ => 1 / (N : ℝ) ^ (s + 1)) := by
    simp only [zero_div, sub_zero]
    exact isBigO_zero _ _
  rw [asympCoeff_of_isBigO hO le_rfl, if_pos rfl]

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
alias asympCoeff_of_eventuallyEq_zero := Puder.BP.PartA.asympCoeff_of_eventuallyEq_zero

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
/-- From the `O`-expansion of Theorem 2.3: the limit exists. -/
theorem tendsto_of_isBigO {G : ℕ → ℝ} {K : ℝ} {k : ℕ}
    (h : (fun N : ℕ => G N - K / (N : ℝ) ^ k) =O[atTop] (fun N : ℕ => 1 / (N : ℝ) ^ (k + 1))) :
    ∃ L, Tendsto G atTop (𝓝 L) :=
  ⟨_, by simpa using tendsto_pow_mul_aux h (Nat.zero_le k)⟩

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
alias tendsto_of_isBigO := Puder.BP.PartA.tendsto_of_isBigO

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
/-- The zpow in Theorem 2.3 is a natural power when `r ≥ 1`. -/
theorem isBigO_natPow {d : ℕ} {w : FreeGroup (Fin d)} {r : ℕ} (hr1 : 1 ≤ r)
    (h : (fun N : ℕ => expFix d w N - 1 - ((Crit w).ncard : ℝ) / (N : ℝ) ^ ((r : ℤ) - 1)) =O[atTop]
        (fun N : ℕ => 1 / (N : ℝ) ^ r)) :
    (fun N : ℕ => (expFix d w N - 1) - ((Crit w).ncard : ℝ) / (N : ℝ) ^ (r - 1)) =O[atTop]
        (fun N : ℕ => 1 / (N : ℝ) ^ (r - 1 + 1)) := by
  have e1 : ((r : ℤ) - 1) = ((r - 1 : ℕ) : ℤ) := by omega
  have e2 : r - 1 + 1 = r := by omega
  simp_rw [e1, zpow_natCast] at h
  rw [e2]
  exact h

/-! ### Part A2: primitivity rank basics -/
theorem freeGroup_fin_zero_eq_one (x : FreeGroup (Fin 0)) : x = 1 := by
  apply FreeGroup.toWord_injective
  rw [FreeGroup.toWord_one]
  rcases h : x.toWord with _ | ⟨a, _⟩
  · rfl
  · exact a.1.elim0

theorem eq_one_of_rank_zero {d : ℕ} {J : Subgroup (FreeGroup (Fin d))}
    (b : FreeGroupBasis (Fin 0) J) {x : FreeGroup (Fin d)} (hx : x ∈ J) : x = 1 := by
  have : b.repr ⟨x, hx⟩ = b.repr 1 := by
    rw [freeGroup_fin_zero_eq_one (b.repr ⟨x, hx⟩), freeGroup_fin_zero_eq_one (b.repr 1)]
  have := congrArg Subtype.val (b.repr.injective this)
  simpa using this

theorem hasRank_top (d : ℕ) : HasRank (⊤ : Subgroup (FreeGroup (Fin d))) d :=
  ⟨(FreeGroupBasis.ofFreeGroup (Fin d)).map Subgroup.topEquiv.symm⟩

theorem one_le_primitivityRank {d : ℕ} {w : FreeGroup (Fin d)} (hw : w ≠ 1) :
    1 ≤ primitivityRank w := by
  unfold primitivityRank
  refine le_iInf₂ fun r hr => ?_
  obtain ⟨J, hwJ, ⟨b⟩, -⟩ := hr
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact absurd (eq_one_of_rank_zero b hwJ) hw
  · exact_mod_cast hr

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
/-! ### Part A2: primitivity rank basics -/
alias one_le_primitivityRank := Puder.BP.PartA.one_le_primitivityRank

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
theorem primitivityRank_le_of_not_isPrimitiveIn_top {d : ℕ} {w : FreeGroup (Fin d)}
    (h : ¬ IsPrimitiveIn ⊤ w) : primitivityRank w ≤ d :=
  iInf₂_le (f := fun (r : ℕ) (_ : ∃ J : Subgroup (FreeGroup (Fin d)),
      w ∈ J ∧ HasRank J r ∧ ¬ IsPrimitiveIn J w) => (r : ℕ∞))
    d ⟨⊤, Subgroup.mem_top w, hasRank_top d, h⟩

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
alias primitivityRank_le_of_not_isPrimitiveIn_top := Puder.BP.PartA.primitivityRank_le_of_not_isPrimitiveIn_top

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
theorem primitivityRank_eq_top_of_forall {d : ℕ} {w : FreeGroup (Fin d)}
    (h : ∀ J : Subgroup (FreeGroup (Fin d)), w ∈ J → IsPrimitiveIn J w) :
    primitivityRank w = ⊤ :=
  le_antisymm le_top (le_iInf₂ fun _ ⟨J, hJ, _, hn⟩ => absurd (h J hJ) hn)

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
alias primitivityRank_eq_top_of_forall := Puder.BP.PartA.primitivityRank_eq_top_of_forall

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
theorem isPrimitiveIn_top_of_primitivityRank_eq_top {d : ℕ} {w : FreeGroup (Fin d)}
    (h : primitivityRank w = ⊤) : IsPrimitiveIn ⊤ w := by
  by_contra hn
  have := primitivityRank_le_of_not_isPrimitiveIn_top hn
  rw [h] at this
  exact absurd this (not_le.mpr (ENat.natCast_lt_top d))

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
alias isPrimitiveIn_top_of_primitivityRank_eq_top := Puder.BP.PartA.isPrimitiveIn_top_of_primitivityRank_eq_top

end Puder.BP
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
theorem length_toWord_wordFree_le {d : ℕ} (w : List (StrongConv.Letter d)) :
    (StrongConv.wordFree w).toWord.length ≤ w.length := by
  induction w with
  | nil => simp [StrongConv.wordFree]
  | cons a w ih =>
    rcases a with _ | (i | i)
    · have hw : StrongConv.wordFree (none :: w) = StrongConv.wordFree w := by
        simp [StrongConv.wordFree]
      rw [hw, List.length_cons]; omega
    · have hw : StrongConv.wordFree (some (Sum.inl i) :: w) =
          FreeGroup.of i * StrongConv.wordFree w := by
        simp [StrongConv.wordFree]
      rw [hw]
      refine ((FreeGroup.toWord_mul_sublist _ _).length_le).trans ?_
      simp [FreeGroup.toWord_of]; omega
    · have hw : StrongConv.wordFree (some (Sum.inr i) :: w) =
          (FreeGroup.of i)⁻¹ * StrongConv.wordFree w := by
        simp [StrongConv.wordFree]
      rw [hw]
      refine ((FreeGroup.toWord_mul_sublist _ _).length_le).trans ?_
      simp [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev]; omega

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
open StrongConv
open scoped InnerProductSpace
/-! ### Part A3: fixed points -/
/-! Copied from the accepted proof of `exists_uniformExp_trN_wordEval_eq_div`. -/
noncomputable def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
noncomputable def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

/-- Number of fixed points. -/
noncomputable def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card

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

lemma wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordEval (sModel σ) w = permOpPerp (wordPerm σ w) := by
  induction w with
  | nil => simp [wordEval, wordPerm, permOpPerp_one]
  | cons a w ih =>
    simp only [wordEval, wordPerm, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, permOpPerp_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [letterPerm, permOpPerp_one]
    · simp [letterPerm, letterOp, sModel]
    · simp [letterPerm, letterOp, sModel, star_permOpPerp]

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
  have hne : onesVec N ≠ 0 := by
    intro h0
    have := congr_arg (fun v : EuclideanSpace ℂ (Fin N) => v ⟨0, hN⟩) h0
    simp [onesVec] at this
  have hr : Module.finrank ℂ K = 1 := finrank_span_singleton hne
  rw [h1, h2, LinearMap.trace_id, hr] at h
  rw [h]
  push_cast
  ring

theorem trN_wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    trN N (wordEval (sModel σ) w) = ((fixCount (wordPerm σ w) : ℝ) - 1) / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [trN]
  rw [trN, wordEval_sModel, trace_permOpPerp hN]
  simp

theorem wordPerm_eq_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordPerm σ w = FreeGroup.lift σ (wordFree w) := by
  rw [wordPerm, wordFree, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rcases a with _ | (i | i) <;> simp [letterPerm]

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP.PartA
theorem mul_uniformExp_trN_eq {d : ℕ} (w : List (StrongConv.Letter d)) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        StrongConv.trN N (StrongConv.wordEval (StrongConv.sModel σ) w)) =
      expFix d (StrongConv.wordFree w) N - 1 := by
  simp only [trN_wordEval_sModel, wordPerm_eq_lift, fixCount, expFix, StrongConv.uniformExp]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hc : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin d → Equiv.Perm (Fin N)) := Fintype.card_pos
    positivity
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  field_simp
  simp

theorem sum_card_fix_perm {N : ℕ} (hN : 1 ≤ N) :
    ∑ τ : Equiv.Perm (Fin N), ((Finset.univ.filter fun x => τ x = x).card : ℝ) =
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
  classical
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Equiv.Perm (Fin N)) (Fin N)
  have h1 : Fintype.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin N)) (Fin N)) = 1 := by
    have hs := (MulAction.pretransitive_iff_subsingleton_quotient (Equiv.Perm (Fin N)) (Fin N)).mp
      inferInstance
    rw [Fintype.card_eq_one_iff]
    exact ⟨Quotient.mk (MulAction.orbitRel (Equiv.Perm (Fin N)) (Fin N)) ⟨0, hN⟩, fun y => Subsingleton.elim _ _⟩
  rw [h1, one_mul] at hB
  rw [← hB, Nat.cast_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Fintype.card_subtype]
  simp [MulAction.mem_fixedBy, Equiv.Perm.smul_def]

theorem expFix_eq_one_of_isPrimitiveIn_top {d : ℕ} {w : FreeGroup (Fin d)}
    (h : IsPrimitiveIn ⊤ w) {N : ℕ} (hN : 1 ≤ N) : expFix d w N = 1 := by
  classical
  obtain ⟨ι, b, i, hi⟩ := h
  set b' := b.map Subgroup.topEquiv with hb'def
  have hb' : b' i = w := hi
  let e : (Fin d → Equiv.Perm (Fin N)) ≃ (ι → Equiv.Perm (Fin N)) :=
    FreeGroup.lift.trans b'.lift.symm
  have he : ∀ σ, e σ i = FreeGroup.lift σ w := fun σ => by
    simp [e, FreeGroupBasis.lift_symm_apply]
    rw [← hb']
    rfl
  have hc : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin d → Equiv.Perm (Fin N)) := Fintype.card_pos
    positivity
  unfold expFix StrongConv.uniformExp
  rw [div_eq_one_iff_eq hc]
  set f : Equiv.Perm (Fin N) → ℝ := fun τ => ((Finset.univ.filter fun x => τ x = x).card : ℝ)
    with hf
  change ∑ σ, f (FreeGroup.lift σ w) = _
  simp_rw [← he]
  rcases Nat.lt_or_ge N 2 with hN1 | hN2
  · obtain rfl : N = 1 := by omega
    have : ∀ τ : Equiv.Perm (Fin 1), f τ = 1 := by
      intro τ
      have hx : ∀ x : Fin 1, τ x = x := fun x => Subsingleton.elim _ _
      simp [hf, hx]
    simp [this]
  · have hρ : (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩) ≠ 1 := by
      intro h1
      have := congrArg (fun π : Equiv.Perm (Fin N) => π ⟨0, by omega⟩) h1
      simp [Equiv.swap_apply_left] at this
    have : Finite (ι → Equiv.Perm (Fin N)) := Finite.of_equiv _ e
    have : Finite ι := by
      refine Finite.of_injective (fun j => Pi.mulSingle j (Equiv.swap (⟨0, by omega⟩ : Fin N)
        ⟨1, by omega⟩)) ?_
      intro j j' hjj
      by_contra hne
      have := congrFun hjj j
      simp [hne] at this
    letI : Fintype ι := Fintype.ofFinite ι
    have hsum : ∑ σ, f (e σ i) = ∑ τ : ι → Equiv.Perm (Fin N), f (τ i) :=
      e.sum_comp (fun τ => f (τ i))
    rw [hsum, ← (Equiv.funSplitAt i (Equiv.Perm (Fin N))).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.funSplitAt_symm_apply, dif_pos, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [Fintype.card_congr e, Fintype.card_congr (Equiv.funSplitAt i (Equiv.Perm (Fin N))),
      Fintype.card_prod]
    have h2 := sum_card_fix_perm hN
    simp only [hf] at h2 ⊢
    rw [← Finset.mul_sum, h2]
    push_cast
    ring

end Puder.BP.PartA
end

section
open Filter Topology Asymptotics
namespace Puder.BP
/-! ### Part A3: fixed points -/
alias expFix_eq_one_of_isPrimitiveIn_top := Puder.BP.PartA.expFix_eq_one_of_isPrimitiveIn_top

alias mul_uniformExp_trN_eq := Puder.BP.PartA.mul_uniformExp_trN_eq

alias length_toWord_wordFree_le := Puder.BP.PartA.length_toWord_wordFree_le

alias isBigO_natPow := Puder.BP.PartA.isBigO_natPow

end Puder.BP
end

section
open Filter Topology Asymptotics
open Puder.BP in
theorem Puder.wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le_dev (d : ℕ)
    (w : List (StrongConv.Letter d))
    (hw : StrongConv.wordFree w ≠ 1) :
    (∀ s : ℕ, (s : ℕ∞) + 2 ≤ Puder.primitivityRank (StrongConv.wordFree w) →
        StrongConv.wordCoeff w s = 0) ∧
      (∀ r : ℕ, Puder.primitivityRank (StrongConv.wordFree w) = r →
        (Puder.Crit (StrongConv.wordFree w)).Finite ∧
          StrongConv.wordCoeff w (r - 1) = (Puder.Crit (StrongConv.wordFree w)).ncard) ∧
      (∀ s : ℕ, Puder.primitivityRank (StrongConv.wordFree w) ≤ s →
        |StrongConv.wordCoeff w s| ≤ (w.length : ℝ) ^ (2 * (s + 1))) ∧
      (Puder.primitivityRank (StrongConv.wordFree w) ≤ d ∨
        Puder.primitivityRank (StrongConv.wordFree w) = ⊤) := by
  set v := StrongConv.wordFree w with hv
  -- `b_s = asympCoeff (expFix - 1)`
  have hG : ∀ s, StrongConv.wordCoeff w s =
      StrongConv.asympCoeff (fun N => expFix d v N - 1) s := by
    intro s
    unfold StrongConv.wordCoeff
    apply asympCoeff_congr
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact mul_uniformExp_trN_eq w hN
  have h4 : Puder.primitivityRank v ≤ d ∨ Puder.primitivityRank v = ⊤ := by
    by_cases hp : Puder.IsPrimitiveIn ⊤ v
    · exact Or.inr (primitivityRank_eq_top_of_forall
        (fun J hJ => Puder.isPrimitiveIn_of_isPrimitiveIn_top hp J hJ))
    · exact Or.inl (primitivityRank_le_of_not_isPrimitiveIn_top hp)
  rcases eq_top_or_lt_top (Puder.primitivityRank v) with htop | hfin
  · -- `π = ∞`: `w` is primitive, `E[#fix] = 1`
    have hp := isPrimitiveIn_top_of_primitivityRank_eq_top htop
    have hz : ∀ s, StrongConv.wordCoeff w s = 0 := by
      intro s
      rw [hG]
      apply asympCoeff_of_eventuallyEq_zero
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [expFix_eq_one_of_isPrimitiveIn_top hp hN]; ring
    refine ⟨fun s _ => hz s, fun r hr => ?_, fun s hs => ?_, h4⟩
    · rw [htop] at hr; exact absurd hr.symm (ENat.natCast_ne_top r)
    · rw [htop] at hs; exact absurd hs (by simp)
  · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hfin.ne
    have hr' : Puder.primitivityRank v = r := hr.symm
    have hr1 : 1 ≤ r := by
      have := one_le_primitivityRank hw
      rw [hr'] at this; exact_mod_cast this
    obtain ⟨hfinC, hO⟩ := Puder.crit_finite_and_isBigO_uniformExp_card_fixedPoints d v r hr'
    have hO' := isBigO_natPow hr1 hO
    have hcoef : ∀ s, s ≤ r - 1 → StrongConv.wordCoeff w s =
        if s = r - 1 then ((Puder.Crit v).ncard : ℝ) else 0 := by
      intro s hs
      rw [hG]
      exact asympCoeff_of_isBigO (G := fun N => expFix d v N - 1) hO' hs
    refine ⟨fun s hs => ?_, fun r' hr'' => ?_, fun s hs => ?_, h4⟩
    · rw [hr'] at hs
      have hs' : s + 2 ≤ r := by exact_mod_cast hs
      rw [hcoef s (by omega), if_neg (by omega)]
    · rw [hr'] at hr''
      have : r' = r := by exact_mod_cast hr''.symm
      subst this
      refine ⟨hfinC, ?_⟩
      rw [hcoef _ le_rfl, if_pos rfl]
    · rw [hr'] at hs
      have hs' : r ≤ s := by exact_mod_cast hs
      obtain ⟨L, hL⟩ := tendsto_of_isBigO hO'
      have hF : Tendsto (fun N => expFix d v N) atTop (𝓝 (L + 1)) := by
        have := hL.add_const 1
        simpa using this
      rw [hG, asympCoeff_sub_const hF 1 (by omega)]
      have hb := Puder.abs_asympCoeff_uniformExp_card_fixedPoints_le d v hw s
        (by rw [hr']; exact_mod_cast hs')
      refine hb.trans ?_
      gcongr
      exact_mod_cast length_toWord_wordFree_le w

end

section
open Filter Topology Asymptotics
theorem solution (d : ℕ)
    (w : List (StrongConv.Letter d))
    (hw : StrongConv.wordFree w ≠ 1) :
    (∀ s : ℕ, (s : ℕ∞) + 2 ≤ Puder.primitivityRank (StrongConv.wordFree w) →
        StrongConv.wordCoeff w s = 0) ∧
      (∀ r : ℕ, Puder.primitivityRank (StrongConv.wordFree w) = r →
        (Puder.Crit (StrongConv.wordFree w)).Finite ∧
          StrongConv.wordCoeff w (r - 1) = (Puder.Crit (StrongConv.wordFree w)).ncard) ∧
      (∀ s : ℕ, Puder.primitivityRank (StrongConv.wordFree w) ≤ s →
        |StrongConv.wordCoeff w s| ≤ (w.length : ℝ) ^ (2 * (s + 1))) ∧
      (Puder.primitivityRank (StrongConv.wordFree w) ≤ d ∨
        Puder.primitivityRank (StrongConv.wordFree w) = ⊤) := by
  exact Puder.wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le_dev d w hw
end

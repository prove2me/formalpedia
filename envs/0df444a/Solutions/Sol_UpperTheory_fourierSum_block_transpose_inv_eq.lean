-- Prove2me | solution 1 for UpperTheory.fourierSum_block_transpose_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:58.942485+00:00
-- url     : https://prove2.me/submissions/24c4378d-242b-4bde-8025-3fe7db57601b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_FourierSumBlockTransposeInvEq
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_smul_stdLat
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_maximalIdeal_eq
import Theorems.Thm_GlobalTheory_SplitFlip_fourierSum_apply
import Theorems.Thm_GlobalTheory_SplitFlip_invT_mem_KO
import Theorems.Thm_GlobalTheory_SplitFlip_invT_val
import Theorems.Thm_GlobalTheory_SplitFlip_liftRes_mem
import Theorems.Thm_GlobalTheory_SplitFlip_pairCols_eq_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise
namespace UpperTheory.FourierBlockTranspose
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem mk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b) ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  constructor
  · rintro ⟨c, hc⟩
    have hc' : (c : k) * (ϖ : k) ^ e = (a : k) - b := by
      simpa using congrArg Subtype.val hc
    rw [← hc', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have : ((ϖ : k) ^ e)⁻¹ * ((c : k) * (ϖ : k) ^ e) = c := by
      field_simp
    rw [this]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
private theorem mul_mem_int {A C B : Type} [Fintype C] {X : Matrix A C k} {Y : Matrix C B k}
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ 𝒪[k]) (i : A) (j : B) : (X * Y) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact sum_mem fun c _ => mul_mem (hX i c) (hY c j)
private theorem sum_res_mul_left {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (f : Matrix A B k → ℂ)
    (hf : ∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z)
    (M : GL A k) (hM : M ∈ KO k A) :
    ∑ S : A → B → Res k e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) =
      ∑ S : A → B → Res k e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  obtain ⟨hMi, hMinv⟩ := (mem_KO_iff M).1 hM
  have hint : ∀ (S : A → B → Res k e) (i : A) (j : B), (M.val * liftRes S) i j ∈ 𝒪[k] :=
    fun S i j => mul_mem_int hMi (liftRes_mem S) i j
  let σ : (A → B → Res k e) → (A → B → Res k e) := fun S i j =>
    Ideal.Quotient.mk _ ⟨(M.val * liftRes S) i j, hint S i j⟩
  have hclose : ∀ (S : A → B → Res k e) (i : A) (j : B),
      (((ϖ ^ e)⁻¹ : kˣ) : k) * (liftRes (σ S) i j - (M.val * liftRes S) i j) ∈ 𝒪[k] := by
    intro S i j
    have h := (mk_eq_iff hϖ e (Quotient.out (σ S i j)) ⟨_, hint S i j⟩).1
      (by rw [Ideal.Quotient.mk_out])
    simpa [liftRes] using h
  have hinj : Function.Injective σ := by
    intro S S' h
    funext i j
    have hd : ∀ a b, ((((ϖ ^ e)⁻¹ : kˣ) : k) • (M.val * (liftRes S - liftRes S'))) a b ∈ 𝒪[k] := by
      intro a b
      have h1 := (mk_eq_iff hϖ e _ _).1 (congrFun (congrFun h a) b)
      simpa [Matrix.mul_sub, Matrix.sub_apply, Matrix.smul_apply] using h1
    have h2 := mul_mem_int hMinv hd i j
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    have h3 := (mk_eq_iff hϖ e (Quotient.out (S i j)) (Quotient.out (S' i j))).2
      (by simpa [liftRes, Matrix.sub_apply, Matrix.smul_apply] using h2)
    rwa [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at h3
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hinj) _ _ ?_
  intro S
  have hsplit : (ϖ ^ e)⁻¹ • liftRes (σ S) = M.val * ((ϖ ^ e)⁻¹ • liftRes S) +
      ((ϖ ^ e)⁻¹ • liftRes (σ S) - M.val * ((ϖ ^ e)⁻¹ • liftRes S)) := by abel
  rw [hsplit, hf]
  intro i j
  rw [Matrix.mul_smul]
  simp only [Units.smul_def, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ← mul_sub]
  exact hclose S i j
end UpperTheory.FourierBlockTranspose
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise
open UpperTheory.FourierBlockTranspose
namespace UpperTheory
theorem _root_.solution :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 → ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ u ∈ KO k A, ∀ Y : Matrix A (D₁ ⊕ D₂) k, fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (fromCols (u.valᵀ * Z.toCols₁) ((u⁻¹).val * Z.toCols₂))) Y = fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ ((u⁻¹).val * Y) := by
  intro k _ _ _ _ A D₁ D₂ _ _ _ _ _ _ ψ ϖ e hϖ hψ Φ hΦ u hu Y
  obtain ⟨huI, huinvI⟩ := (mem_KO_iff u).1 hu
  have hmulcond : ∀ g : Matrix A A k, (∀ i j, g i j ∈ 𝒪[k]) → ∀ Z : Matrix A (D₁ ⊕ D₂) k,
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Z i j ∈ 𝒪[k]) →
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * (g * Z) i j ∈ 𝒪[k]) := by
    intro g hg Z hZ i j hj
    have h := mul_mem_int hg
      (Y := Matrix.of fun (a : A) (b : Assignment.one.block D₁ D₂) => ((ϖ ^ e : kˣ) : k) * Z a b)
      (fun a b => hZ a b b.2) i ⟨j, hj⟩
    rw [Matrix.mul_apply] at h
    rw [Matrix.mul_apply, Finset.mul_sum]
    convert h using 2 with l
    simp only [Matrix.of_apply]
    ring
  have hcond : (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * ((u⁻¹).val * Y) i j ∈ 𝒪[k]) := by
    constructor
    · exact hmulcond _ huinvI Y
    · intro h
      have h2 := hmulcond _ huI _ h
      rwa [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2
  rw [fourierSum_apply, fourierSum_apply]
  by_cases hc : ∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k]
  swap
  · rw [if_neg hc, if_neg (mt hcond.2 hc)]
  rw [if_pos hc, if_pos (hcond.1 hc)]
  have hc' := hcond.1 hc
  congr 1
  have hψ1 : ∀ y : k, y ∈ 𝒪[k] → ψ y = 1 := by
    intro y hy
    have h := (hψ (1 : k)).2 (by simp)
    apply h
    rw [map_one]
    exact (Valuation.mem_integer_iff _ _).1 hy
  have hmat : ∀ L : Matrix A (Assignment.one.block D₁ D₂) k,
      fromCols (u.valᵀ * (setCols (Assignment.one.block D₁ D₂) Y L).toCols₁)
        ((u⁻¹).val * (setCols (Assignment.one.block D₁ D₂) Y L).toCols₂) =
      setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) (u.valᵀ * L) := by
    intro L
    ext i j
    rcases j with d | d
    · simp [setCols, Assignment.block, Matrix.mul_apply]
      rfl
    · simp [setCols, Assignment.block, Matrix.mul_apply]
  have hpair : ∀ L : Matrix A (Assignment.one.block D₁ D₂) k,
      pairCols (Assignment.one.block D₁ D₂) Y L =
        pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) (u.valᵀ * L) := by
    intro L
    rw [pairCols_eq_trace, pairCols_eq_trace]
    have hs : ((u⁻¹).val * Y).submatrix id Subtype.val =
        (u⁻¹).val * Y.submatrix id (Subtype.val : Assignment.one.block D₁ D₂ → D₁ ⊕ D₂) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hs, Matrix.transpose_mul, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm (u.valᵀ * L * (Y.submatrix id Subtype.val)ᵀ),
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv,
      Matrix.transpose_one, Matrix.one_mul]
  let f : Matrix A (Assignment.one.block D₁ D₂) k → ℂ := fun W =>
    Φ (setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • W)) *
      (ψ (pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • W)) : ℂ)
  have hΦ' : HasDepth ϖ e (stdLat k (D₁ ⊕ D₂)) Φ := hΦ
  obtain ⟨_, hΦinv⟩ := hΦ'
  have hf : ∀ Z Z' : Matrix A (Assignment.one.block D₁ D₂) k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z := by
    intro Z Z' hZ'
    simp only [f]
    rw [smul_add]
    have hset : setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z + (ϖ ^ e) • Z') =
        setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z) +
          setCols (Assignment.one.block D₁ D₂) 0 ((ϖ ^ e) • Z') := by
      ext i j
      simp only [setCols, Matrix.of_apply, Matrix.add_apply]
      split_ifs <;> simp
    have hlat : setCols (Assignment.one.block D₁ D₂) 0 ((ϖ ^ e) • Z') ∈
        matLat A (ϖ ^ e • stdLat k (D₁ ⊕ D₂)) := by
      rw [FourierDepth.mem_matLat_smul_stdLat]
      intro i j
      simp only [setCols, Matrix.of_apply]
      split_ifs with h
      · rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, map_mul]
        exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hZ' i ⟨j, h⟩))
      · simp
    have hpadd : pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z + (ϖ ^ e) • Z') =
        pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z) +
          pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z') := by
      simp only [pairCols, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    have hmemb : pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z') ∈ 𝒪[k] := by
      simp only [pairCols]
      refine sum_mem fun i _ => sum_mem fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, mul_comm ((ϖ ^ e : kˣ) : k) _, mul_assoc]
      exact mul_mem (hZ' i j) (hc' i j j.2)
    rw [hset, hΦinv _ _ hlat, hpadd, AddChar.map_add_eq_mul, hψ1 _ hmemb, mul_one]
  have key := sum_res_mul_left ϖ e hϖ f hf (invT u⁻¹) (invT_mem_KO (inv_mem hu))
  calc _ = ∑ T : A → Assignment.one.block D₁ D₂ → Res k e,
        f ((invT u⁻¹).val * ((ϖ ^ e)⁻¹ • liftRes T)) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        simp only [f]
        rw [invT_val, inv_inv, Matrix.mul_smul, smul_inv_smul, ← hmat, ← hpair]
    _ = ∑ T : A → Assignment.one.block D₁ D₂ → Res k e, f ((ϖ ^ e)⁻¹ • liftRes T) := key
    _ = _ := by
        refine Finset.sum_congr rfl fun T _ => ?_
        simp only [f, smul_inv_smul]
end UpperTheory

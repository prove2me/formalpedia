-- Prove2me | solution 1 for UnipMove.GraphH.maj_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:07.976684+00:00
-- url     : https://prove2.me/submissions/8f3f8dbe-5c20-4af5-9a39-399d9b0ca117

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Theorems.Thm_UnipMove_GraphH_re_conj_mul
import Theorems.Thm_UnipMove_GraphH_sum_splitR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
section Blocks
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
end Blocks
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma sum_four_comm_unipotent_moves {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → M) :
    ∑ a, ∑ b, ∑ j, ∑ k, F a b j k = ∑ j, ∑ k, ∑ a, ∑ b, F a b j k := by
  calc ∑ a, ∑ b, ∑ j, ∑ k, F a b j k = ∑ a, ∑ j, ∑ b, ∑ k, F a b j k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ k, ∑ b, F a b j k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ k, ∑ b, F a b j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ a, ∑ b, F a b j k :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
private lemma hermC_mulVec_mulVec_eq_sum_gram' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (c d : Fin r → ℂ) :
    hermC τ G (M *ᵥ c) (M *ᵥ d) = ∑ j, ∑ k, c j * gram τ G M j k * conj (d k) := by
  have e1 : ∀ a b, (M *ᵥ c) a * τ (G a b) * conj ((M *ᵥ d) b) =
      ∑ j, ∑ k, M a j * c j * τ (G a b) * (conj (M b k) * conj (d k)) := by
    intro a b
    rw [show (M *ᵥ c) a = ∑ j, M a j * c j from rfl, show (M *ᵥ d) b = ∑ k, M b k * d k from rfl,
      map_sum, Finset.sum_mul, Finset.sum_mul_sum]
    simp only [map_mul]
  have e2 : ∀ j k, c j * gram τ G M j k * conj (d k) =
      ∑ a, ∑ b, c j * (M a j * τ (G a b) * conj (M b k)) * conj (d k) := by
    intro j k
    rw [show gram τ G M j k = ∑ a, ∑ b, M a j * τ (G a b) * conj (M b k) from rfl,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
  unfold hermC
  simp only [e1, e2]
  rw [sum_four_comm_unipotent_moves]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private lemma col_eq_mulVec_single (M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    col M j = M *ᵥ Pi.single j 1 := by
  funext k
  first
    | simp [col, Matrix.mulVec, dotProduct, Pi.single_apply]
    | simp [col, Matrix.mulVec_single_one]
    | (rw [Matrix.mulVec_single_one]; rfl)
private lemma hermC_mat_mulVec_eq_sum_sgn_of_isOrtho {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (c d : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ c) (mat x τ *ᵥ d) =
      ∑ j, c j * ((sgn X.p0 j : ℝ) : ℂ) * conj (d j) := by
  rw [hermC_mulVec_mulVec_eq_sum_gram', ho τ]
  first
    | simp only [Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    | simp [Matrix.diagonal_apply]
end Frames
end
end UnipMove.GraphH
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
end UnipMove
end

set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.GraphH
theorem _root_.solution {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (c : Fin r → ℂ) :
    X.maj x τ (mat x τ *ᵥ c) = nsq c := by
  have hgp : X.gramPos x τ = 1 := by
    ext a b
    simp [Data.gramPos, ho τ, Matrix.diagonal_apply, Matrix.one_apply, sgn, Fin.ext_iff]
  have hcol : ∀ j, hermC τ.1 X.Gm (mat x τ *ᵥ c) (col (mat x τ) j) =
      c j * ((sgn X.p0 j : ℝ) : ℂ) := by
    intro j
    rw [col_eq_mulVec_single, hermC_mat_mulVec_eq_sum_sgn_of_isOrtho X ho]
    simp [Pi.single_apply]
  have hpos : X.posPart x τ (mat x τ *ᵥ c) = ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 := by
    unfold Data.posPart
    rw [hgp, inv_one]
    simp only [hcol, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hs : ((sgn X.p0 (Fin.castLE X.p0_le a : ℕ) : ℝ) : ℂ) = 1 := by simp [sgn]
    rw [hs, mul_one]
    rw [show c (Fin.castLE X.p0_le a) * conj (c (Fin.castLE X.p0_le a)) =
        conj (c (Fin.castLE X.p0_le a)) * (c (Fin.castLE X.p0_le a) * ((1 : ℝ) : ℂ)) by
          simp [mul_comm], re_conj_mul, one_mul]
  have hh : (hermC τ.1 X.Gm (mat x τ *ᵥ c) (mat x τ *ᵥ c)).re =
      ∑ j : Fin r, sgn X.p0 j * ‖c j‖ ^ 2 := by
    rw [hermC_mat_mulVec_eq_sum_sgn_of_isOrtho X ho, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show c j * ((sgn X.p0 j : ℝ) : ℂ) * conj (c j) =
        conj (c j) * (c j * ((sgn X.p0 j : ℝ) : ℂ)) by ring, re_conj_mul]
  unfold Data.maj
  rw [hpos, hh, sum_splitR X (fun j => sgn X.p0 j * ‖c j‖ ^ 2)]
  unfold nsq
  rw [sum_splitR X (fun j => ‖c j‖ ^ 2)]
  have h1 : ∀ a : Fin X.p0, sgn X.p0 (Fin.castLE X.p0_le a : ℕ) = 1 := fun a => by simp [sgn]
  have h2 : ∀ m : Fin (r - X.p0), sgn X.p0 (nI X m : ℕ) = -1 := fun m => by
    unfold sgn
    rw [if_neg]
    show ¬ (X.p0 + (m : ℕ) < X.p0)
    omega
  simp only [h1, h2, one_mul, neg_one_mul, Finset.sum_neg_distrib]
  ring
end UnipMove.GraphH

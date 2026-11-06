-- Prove2me | solution 1 for TsengCGD.Linear.theorem2_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:05:41.066834+00:00
-- url     : https://prove2.me/submissions/2e14f5fc-c81e-4661-aca2-d68975e90bdd

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
import Theorems.Thm_TsengCGD_Global_theorem1_a
import Theorems.Thm_TsengCGD_Linear_lemma5_a
import Theorems.Thm_TsengCGD_Linear_theorem1_f
import Theorems.Thm_TsengCGD_Linear_theorem2_a
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace
open TsengCGD.Global TsengCGD.Linear


lemma cgd2_inner_eq {n : ℕ} (u v : Vec n) : ⟪u, v⟫ = ∑ j, u j * v j := by
  simp [PiLp.inner_apply, mul_comm]

lemma cgd2_norm_sq {n : ℕ} (u : Vec n) : ‖u‖ ^ 2 = ∑ j, u j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp

lemma cgd2_taylor {n : ℕ} (f : Vec n → ℝ) (D U : Set (Vec n)) (hU : IsOpen U) (hDU : D ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hD : Convex ℝ D) (L : ℝ) (hL : GradLipOn f D L)
    (x y : Vec n) (hx : x ∈ D) (hy : y ∈ D) :
    |f y - f x - ⟪gradient f x, y - x⟫| ≤ L * ‖y - x‖ ^ 2 := by
  set g : Vec n → ℝ := fun z => f z - InnerProductSpace.toDual ℝ (Vec n) (gradient f x) z with hg
  have hseg : segment ℝ x y ⊆ D := hD.segment_subset hx hy
  have hderiv : ∀ z ∈ segment ℝ x y, HasFDerivWithinAt g
      (InnerProductSpace.toDual ℝ (Vec n) (gradient f z) -
        InnerProductSpace.toDual ℝ (Vec n) (gradient f x)) (segment ℝ x y) z := by
    intro z hz
    have hzU : z ∈ U := hDU (hseg hz)
    have hdiff : DifferentiableAt ℝ f z :=
      (hf.differentiableOn one_ne_zero z hzU).differentiableAt (hU.mem_nhds hzU)
    have h1 := hdiff.hasGradientAt.hasFDerivAt
    have h2 := (InnerProductSpace.toDual ℝ (Vec n) (gradient f x)).hasFDerivAt (x := z)
    exact (h1.sub h2).hasFDerivWithinAt
  have hbound : ∀ z ∈ segment ℝ x y, ‖InnerProductSpace.toDual ℝ (Vec n) (gradient f z) -
        InnerProductSpace.toDual ℝ (Vec n) (gradient f x)‖ ≤ L * ‖y - x‖ := by
    intro z hz
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    calc ‖gradient f z - gradient f x‖ ≤ L * ‖z - x‖ := hL.2 z (hseg hz) x hx
      _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hL.1
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have heq : g y - g x = f y - f x - ⟪gradient f x, y - x⟫ := by
    simp only [hg, InnerProductSpace.toDual_apply_apply, inner_sub_right]; ring
  rw [heq, Real.norm_eq_abs] at this
  calc _ ≤ L * ‖y - x‖ * ‖y - x‖ := this
    _ = L * ‖y - x‖ ^ 2 := by ring

/-- Stationarity gives the variational inequality. -/
lemma cgd2_VI {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (hs : Standing f D P c) (xb : Vec n) (hst : IsStationary f D P c xb) (y : Vec n) (hy : y ∈ D) :
    0 ≤ ⟪gradient f xb, y - xb⟫ + c * P y - c * P xb := by
  obtain ⟨hxb, hst⟩ := hst
  obtain ⟨U, hU, hDU, hf⟩ := hs.smooth
  obtain ⟨_, hDc, hPc, _⟩ := hs.properConvexLsc
  by_contra hneg
  push Not at hneg
  set ε := -(⟪gradient f xb, y - xb⟫ + c * P y - c * P xb) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hdiff : DifferentiableAt ℝ f xb :=
    (hf.differentiableOn one_ne_zero xb (hDU hxb)).differentiableAt (hU.mem_nhds (hDU hxb))
  -- directional derivative
  have hdir : HasDerivAt (fun a : ℝ => f (xb + a • (y - xb))) ⟪gradient f xb, y - xb⟫ 0 := by
    have h1 : HasDerivAt (fun a : ℝ => xb + a • (y - xb)) (y - xb) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - xb)).const_add xb
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ (Vec n) (gradient f xb)) (xb + (0:ℝ) • (y - xb)) := by
      rw [zero_smul, add_zero]; exact hdiff.hasGradientAt.hasFDerivAt
    have := h2.comp_hasDerivAt (0:ℝ) h1
    rw [InnerProductSpace.toDual_apply_apply] at this
    exact this
  have hslope := hdir.tendsto_slope_zero_right
  have hev1 : ∀ᶠ a in 𝓝[>] (0:ℝ), a⁻¹ • (f (xb + (0 + a) • (y - xb)) - f (xb + (0:ℝ) • (y - xb)))
      < ⟪gradient f xb, y - xb⟫ + ε :=
    hslope (Iio_mem_nhds (by linarith))
  have hev2 := hst (y - xb) ε hεpos
  have hev3 : ∀ᶠ a in 𝓝[>] (0:ℝ), a < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with a ha using ha.2
  have hev4 : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨a, h1, h2, h3, h4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  have e : xb + a • (y - xb) = (1 - a) • xb + a • y := by module
  have hmem : xb + a • (y - xb) ∈ D := by
    rw [e]; exact hDc hxb hy (by linarith : (0:ℝ) ≤ 1 - a) (le_of_lt h4) (by ring)
  have hPconv : P (xb + a • (y - xb)) ≤ (1 - a) * P xb + a * P y := by
    have := hPc.2 hxb hy (by linarith : (0:ℝ) ≤ 1 - a) (le_of_lt h4) (by ring)
    rw [e]; simpa [smul_eq_mul] using this
  have h2' := h2 hmem
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at h1
  unfold Fc at h2'
  rw [le_div_iff₀ h4] at h2'
  have h1' : f (xb + a • (y - xb)) - f xb < a * (⟪gradient f xb, y - xb⟫ + ε) := by
    rw [← inv_mul_lt_iff₀ h4]; exact h1
  have hc := hs.c_pos
  nlinarith [mul_le_mul_of_nonneg_left hPconv hc.le]

lemma cgd2_sum_le {n : ℕ} (J : Finset (Fin n)) (a w : Vec n) :
    ∑ j ∈ J, a j * w j ≤ (‖a‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
  rw [cgd2_norm_sq, cgd2_norm_sq, ← Finset.sum_add_distrib, Finset.sum_div]
  calc ∑ j ∈ J, a j * w j ≤ ∑ j ∈ J, (a j ^ 2 + w j ^ 2) / 2 :=
        Finset.sum_le_sum (fun j _ => by nlinarith [sq_nonneg (a j - w j)])
    _ ≤ ∑ j, (a j ^ 2 + w j ^ 2) / 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => by positivity)

lemma cgd2_Hbound {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (lamBar : ℝ)
    (hlb : 0 ≤ lamBar) (hup : ∀ z : Vec n, qf H z ≤ lamBar * ‖z‖ ^ 2)
    (hnn : ∀ z : Vec n, 0 ≤ qf H z) (J : Finset (Fin n)) (d w : Vec n) :
    -∑ j ∈ J, (H *ᵥ WithLp.ofLp d) j * w j ≤ lamBar * (‖d‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
  set w' : Vec n := WithLp.toLp 2 (fun j => if j ∈ J then w j else 0) with hw'
  have hX : ∑ j ∈ J, (H *ᵥ WithLp.ofLp d) j * w j = (H *ᵥ WithLp.ofLp d) ⬝ᵥ WithLp.ofLp w' := by
    simp only [dotProduct, hw']
    rw [← Finset.sum_subset (Finset.subset_univ J)]
    · apply Finset.sum_congr rfl; intro j hj; simp [hj]
    · intro j _ hj; simp [hj]
  have hsym : Hᵀ = H := by
    have := hH.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsym2 : WithLp.ofLp w' ⬝ᵥ (H *ᵥ WithLp.ofLp d) = WithLp.ofLp d ⬝ᵥ (H *ᵥ WithLp.ofLp w') := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]
  have hq := hnn (d + w')
  have hexp : qf H (d + w') = qf H d + 2 * ((H *ᵥ WithLp.ofLp d) ⬝ᵥ WithLp.ofLp w') + qf H w' := by
    simp only [qf, WithLp.ofLp_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [← hsym2, dotProduct_comm (H *ᵥ WithLp.ofLp d) (WithLp.ofLp w')]; ring
  have hw'n : ‖w'‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [cgd2_norm_sq, cgd2_norm_sq]
    apply Finset.sum_le_sum; intro j _
    simp only [hw', PiLp.toLp_apply]; split_ifs <;> nlinarith [sq_nonneg (w j)]
  have h1 := hup d
  have h2 := hup w'
  rw [hX]
  nlinarith [mul_le_mul_of_nonneg_left hw'n hlb]

section cycle
variable {n : ℕ} (J : ℕ → Finset (Fin n)) (x d : ℕ → Vec n) (α : ℕ → ℝ) (k m : ℕ)

lemma cgd2_agree
    (hdisj : ((Finset.Ico k m : Finset ℕ) : Set ℕ).PairwiseDisjoint J)
    (hstep : ∀ ℓ, x (ℓ + 1) = x ℓ + α ℓ • d ℓ) (hsupp : ∀ ℓ, SupportedOn (J ℓ) (d ℓ))
    (p : ℕ) (hp : p ∈ Finset.Ico k m) (j : Fin n) (hj : j ∈ J p) :
    ∀ q, p + 1 ≤ q → q ≤ m → x q j = x (p + 1) j := by
  intro q hq1 hq2
  induction q, hq1 using Nat.le_induction with
  | base => rfl
  | succ q hq ih =>
    have hqm : q < m := by omega
    rw [hstep q]
    have hqI : q ∈ Finset.Ico k m := by
      simp only [Finset.mem_Ico] at hp ⊢; omega
    have hne : p ≠ q := by omega
    have hd : Disjoint (J p) (J q) := hdisj hp hqI hne
    have hjq : j ∉ J q := Finset.disjoint_left.mp hd hj
    have := hsupp q j hjq
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, this, mul_zero, add_zero]
    exact ih (by omega)

lemma cgd2_card (hkm : k ≤ m)
    (hdisj : ((Finset.Ico k m : Finset ℕ) : Set ℕ).PairwiseDisjoint J)
    (hcov : (Finset.Ico k m).biUnion J = Finset.univ) (hne : ∀ ℓ, (J ℓ).Nonempty) :
    m - k ≤ n := by
  have h1 := Finset.card_biUnion hdisj
  rw [hcov, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ∑ u ∈ Finset.Ico k m, 1 ≤ ∑ u ∈ Finset.Ico k m, (J u).card :=
    Finset.sum_le_sum (fun u _ => (hne u).card_pos)
  simp at h2
  omega

lemma cgd2_dist (hstep : ∀ ℓ, x (ℓ + 1) = x ℓ + α ℓ • d ℓ) (hα0 : ∀ ℓ, 0 < α ℓ)
    (hα1 : ∀ ℓ, α ℓ ≤ 1) : ∀ ℓ, k ≤ ℓ → ‖x ℓ - x k‖ ≤ ∑ p ∈ Finset.Ico k ℓ, ‖d p‖ := by
  intro ℓ hℓ
  induction ℓ, hℓ using Nat.le_induction with
  | base => simp
  | succ q hq ih =>
    rw [Finset.sum_Ico_succ_top hq, hstep q]
    have : ‖α q • d q‖ ≤ ‖d q‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hα0 q)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hα1 q)
    calc ‖x q + α q • d q - x k‖ = ‖(x q - x k) + α q • d q‖ := by congr 1; abel
      _ ≤ ‖x q - x k‖ + ‖α q • d q‖ := norm_add_le _ _
      _ ≤ _ := by linarith

lemma cgd2_inner_split
    (hdisj : ((Finset.Ico k m : Finset ℕ) : Set ℕ).PairwiseDisjoint J)
    (hcov : (Finset.Ico k m).biUnion J = Finset.univ)
    (hstep : ∀ ℓ, x (ℓ + 1) = x ℓ + α ℓ • d ℓ) (hsupp : ∀ ℓ, SupportedOn (J ℓ) (d ℓ))
    (a xb : Vec n) :
    ⟪a, x m - xb⟫ = ∑ ℓ ∈ Finset.Ico k m, ∑ j ∈ J ℓ, a j * (x (ℓ + 1) j - xb j) := by
  classical
  rw [cgd2_inner_eq, ← hcov, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  apply Finset.sum_congr rfl
  intro j hj
  have hℓm : ℓ + 1 ≤ m := by simp only [Finset.mem_Ico] at hℓ; omega
  rw [PiLp.sub_apply, cgd2_agree J x d α k m hdisj hstep hsupp ℓ hℓ j hj m hℓm le_rfl]

lemma cgd2_P_split (D : Set (Vec n)) (P : Vec n → ℝ) (hkm : k ≤ m)
    (hdisj : ((Finset.Ico k m : Finset ℕ) : Set ℕ).PairwiseDisjoint J)
    (hcov : (Finset.Ico k m).biUnion J = Finset.univ)
    (DJ : ℕ → Set (Vec n)) (PJ : ℕ → Vec n → ℝ) (DJC : ℕ → Set (Vec n)) (PJC : ℕ → Vec n → ℝ)
    (hw : ∀ ℓ, IsBlockSepWitness D P (J ℓ) (DJ ℓ) (PJ ℓ) (DJC ℓ) (PJC ℓ))
    (y xb : Vec n) (hy : y ∈ D) (hxb : xb ∈ D) :
    P y - P xb = ∑ ℓ ∈ Finset.Ico k m, (PJ ℓ y - PJ ℓ xb) := by
  classical
  let z : ℕ → Vec n := fun s =>
    WithLp.toLp 2 (fun j => if j ∈ (Finset.Ico k s).biUnion J then y j else xb j)
  have key : ∀ s, k ≤ s → s ≤ m → z s ∈ D ∧
      P (z s) - P xb = ∑ ℓ ∈ Finset.Ico k s, (PJ ℓ y - PJ ℓ xb) := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      intro _
      have : z k = xb := by
        ext j; simp [z]
      simp [this, hxb]
    | succ s hs ih =>
      intro hsm
      obtain ⟨hzD, hzP⟩ := ih (by omega)
      have hsI : s ∈ Finset.Ico k m := by simp only [Finset.mem_Ico]; omega
      -- membership facts
      have hnot : ∀ j ∈ J s, j ∉ (Finset.Ico k s).biUnion J := by
        intro j hj hj'
        obtain ⟨ℓ, hℓ, hjℓ⟩ := Finset.mem_biUnion.mp hj'
        have hℓI : ℓ ∈ Finset.Ico k m := by
          simp only [Finset.mem_Ico] at hℓ ⊢; omega
        have hne : ℓ ≠ s := by simp only [Finset.mem_Ico] at hℓ; omega
        exact Finset.disjoint_left.mp (hdisj hℓI hsI hne) hjℓ hj
      have hbu : (Finset.Ico k (s + 1)).biUnion J = (Finset.Ico k s).biUnion J ∪ J s := by
        rw [← Nat.succ_eq_add_one, Nat.Ico_succ_right_eq_insert_Ico hs, Finset.biUnion_insert,
          Finset.union_comm]
      have hi : ∀ j ∈ J s, z (s + 1) j = y j := by
        intro j hj; simp only [z, hbu, Finset.mem_union, hj, or_true, if_true]
      have hii : ∀ j, j ∉ J s → z (s + 1) j = z s j := by
        intro j hj; simp only [z, hbu, Finset.mem_union, hj, or_false]
      have hiii : ∀ j ∈ J s, z s j = xb j := by
        intro j hj; simp only [z, hnot j hj, if_false]
      obtain ⟨_, _, hJdep, hJCdep, hDiff, hPsum⟩ := hw s
      have a1 := hJdep (z (s + 1)) y hi
      have a2 := hJCdep (z (s + 1)) (z s) hii
      have a3 := hJdep (z s) xb hiii
      have hyD := (hDiff y).1 hy
      have hzsD := (hDiff (z s)).1 hzD
      have hz1D : z (s + 1) ∈ D := (hDiff _).2 ⟨a1.1.2 hyD.1, a2.1.2 hzsD.2⟩
      refine ⟨hz1D, ?_⟩
      rw [Finset.sum_Ico_succ_top hs, ← hzP, hPsum _ hz1D, hPsum _ hzD, a1.2, a2.2, a3.2]
      ring
  obtain ⟨_, h⟩ := key m hkm le_rfl
  have : z m = y := by
    ext j; simp [z, hcov]
  rw [this] at h; exact h
end cycle

lemma cgd2_cycle {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (hs : Standing f D P c) (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α : ℕ → ℝ)
    (hxD : ∀ ℓ, x ℓ ∈ D) (hJne : ∀ ℓ, (J ℓ).Nonempty) (hHpd : ∀ ℓ, (H ℓ).PosDef)
    (hdir : ∀ ℓ, IsDir f D P c (H ℓ) (x ℓ) (J ℓ) (d ℓ))
    (hstep : ∀ ℓ, x (ℓ + 1) = x ℓ + α ℓ • d ℓ) (hα0 : ∀ ℓ, 0 < α ℓ) (hα1 : ∀ ℓ, α ℓ ≤ 1)
    (lam lamBar : ℝ) (hA1 : Assumption1 H lam lamBar) (L : ℝ) (hL : GradLipOn f D L)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (DJ : ℕ → Set (Vec n)) (PJ : ℕ → Vec n → ℝ) (DJC : ℕ → Set (Vec n)) (PJC : ℕ → Vec n → ℝ)
    (hw : ∀ ℓ, IsBlockSepWitness D P (J ℓ) (DJ ℓ) (PJ ℓ) (DJC ℓ) (PJC ℓ))
    (k m : ℕ) (hkm : k ≤ m)
    (hdisj : ((Finset.Ico k m : Finset ℕ) : Set ℕ).PairwiseDisjoint J)
    (hcov : (Finset.Ico k m).biUnion J = Finset.univ)
    (xb : Vec n) (hxb : xb ∈ D) :
    Fc f P c (x m) - Fc f P c xb ≤
      (L + n * ((L ^ 2 + 1) / 2 + lamBar)) * (‖x k - xb‖ + ∑ ℓ ∈ Finset.Ico k m, ‖d ℓ‖) ^ 2 +
        ∑ ℓ ∈ Finset.Ico k m, (α ℓ - 1) * ((1 - γ) * qf (H ℓ) (d ℓ) +
          Delta f P c γ (H ℓ) (x ℓ) (d ℓ)) := by
  obtain ⟨hlam, hlamle, hA⟩ := hA1
  have hlb : 0 ≤ lamBar := by linarith
  have hsupp : ∀ ℓ, SupportedOn (J ℓ) (d ℓ) := fun ℓ => (hdir ℓ).1
  set r := ∑ ℓ ∈ Finset.Ico k m, ‖d ℓ‖ with hr
  set R := ‖x k - xb‖ + r with hR
  have hr0 : 0 ≤ r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hR0 : 0 ≤ R := by positivity
  have hxR : ∀ ℓ, k ≤ ℓ → ℓ ≤ m → ‖x ℓ - xb‖ ≤ R := by
    intro ℓ h1 h2
    have := cgd2_dist x d α k hstep hα0 hα1 ℓ h1
    have h3 : ∑ p ∈ Finset.Ico k ℓ, ‖d p‖ ≤ r :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right h2)
        (fun _ _ _ => norm_nonneg _)
    calc ‖x ℓ - xb‖ ≤ ‖x ℓ - x k‖ + ‖x k - xb‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ R := by rw [hR]; linarith
  have hdR : ∀ ℓ ∈ Finset.Ico k m, ‖d ℓ‖ ≤ R := by
    intro ℓ hℓ
    have := Finset.single_le_sum (f := fun ℓ => ‖d ℓ‖) (fun _ _ => norm_nonneg _) hℓ
    rw [hR]; linarith [norm_nonneg (x k - xb)]
  obtain ⟨U, hU, hDU, hf⟩ := hs.smooth
  have hDc : Convex ℝ D := hs.properConvexLsc.2.1
  -- Taylor
  have htay := cgd2_taylor f D U hU hDU hf hDc L hL xb (x m) hxb (hxD m)
  have htay' : f (x m) - f xb - ⟪gradient f xb, x m - xb⟫ ≤ L * R ^ 2 := by
    have h1 := (abs_le.mp htay).2
    have h2 := hxR m hkm le_rfl
    have h3 : ‖x m - xb‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [hL.1]
  -- P split
  have hPs := cgd2_P_split J k m D P hkm hdisj hcov DJ PJ DJC PJC hw (x m) xb (hxD m) hxb
  have hPs' : P (x m) - P xb = ∑ ℓ ∈ Finset.Ico k m, (PJ ℓ (x (ℓ + 1)) - PJ ℓ xb) := by
    rw [hPs]; apply Finset.sum_congr rfl; intro ℓ hℓ
    have hℓm : ℓ + 1 ≤ m := by simp only [Finset.mem_Ico] at hℓ; omega
    have := ((hw ℓ).2.2.1 (x m) (x (ℓ + 1))
      (fun j hj => cgd2_agree J x d α k m hdisj hstep hsupp ℓ hℓ j hj m hℓm le_rfl)).2
    rw [this]
  have hin := cgd2_inner_split J x d α k m hdisj hcov hstep hsupp (gradient f xb) xb
  -- per block bound
  set K0 := (L ^ 2 + 1) / 2 + lamBar with hK0
  have hblock : ∀ ℓ ∈ Finset.Ico k m,
      (∑ j ∈ J ℓ, gradient f xb j * (x (ℓ + 1) j - xb j)) + c * (PJ ℓ (x (ℓ + 1)) - PJ ℓ xb) ≤
        K0 * R ^ 2 + (α ℓ - 1) * ((1 - γ) * qf (H ℓ) (d ℓ) + Delta f P c γ (H ℓ) (x ℓ) (d ℓ)) := by
    intro ℓ hℓ
    have hℓ1 : k ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
    have hℓ2 : ℓ < m := (Finset.mem_Ico.mp hℓ).2
    have hxbJ : xb ∈ DJ ℓ := (((hw ℓ).2.2.2.2.1 xb).1 hxb).1
    have h5 := lemma5_a f D P c hs (x ℓ) (hxD ℓ) (H ℓ) (hHpd ℓ) (J ℓ) (hJne ℓ) (d ℓ) (hdir ℓ)
      γ hγ0 hγ1 (DJ ℓ) (PJ ℓ) (DJC ℓ) (PJC ℓ) (hw ℓ) xb hxbJ (α ℓ) (hα0 ℓ) (hα1 ℓ)
    rw [← hstep ℓ] at h5
    set w := x (ℓ + 1) - xb with hw_def
    set a := gradient f xb - gradient f (x ℓ) with ha
    have hsplit : ∑ j ∈ J ℓ, gradient f xb j * (x (ℓ + 1) j - xb j) =
        ∑ j ∈ J ℓ, a j * w j - ∑ j ∈ J ℓ, (H ℓ *ᵥ WithLp.ofLp (d ℓ)) j * w j +
          ∑ j ∈ J ℓ, (gradient f (x ℓ) j + (H ℓ *ᵥ WithLp.ofLp (d ℓ)) j) * (x (ℓ + 1) j - xb j) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      simp only [hw_def, ha, PiLp.sub_apply]; ring
    have hs1 := cgd2_sum_le (J ℓ) a w
    have hs2 := cgd2_Hbound (H ℓ) (hHpd ℓ) lamBar hlb (fun z => (hA ℓ z).2)
      (fun z => le_trans (by positivity) (hA ℓ z).1) (J ℓ) (d ℓ) w
    have hwR : ‖w‖ ≤ R := hxR (ℓ + 1) (by omega) (by omega)
    have haR : ‖a‖ ≤ L * R := by
      calc ‖a‖ ≤ L * ‖xb - x ℓ‖ := hL.2 xb hxb (x ℓ) (hxD ℓ)
        _ ≤ L * R := by
          apply mul_le_mul_of_nonneg_left _ hL.1
          rw [norm_sub_rev]; exact hxR ℓ hℓ1 hℓ2.le
    have hdR' := hdR ℓ hℓ
    have e1 : ‖a‖ ^ 2 ≤ (L * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) haR 2
    have e2 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwR 2
    have e3 : ‖d ℓ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdR' 2
    rw [hsplit]
    have e4 : lamBar * (‖d ℓ‖ ^ 2 + ‖w‖ ^ 2) ≤ lamBar * (R ^ 2 + R ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hlb
    rw [hK0]
    nlinarith
  have hsum := Finset.sum_le_sum hblock
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard : ((m - k : ℕ) : ℝ) ≤ n := by exact_mod_cast cgd2_card J k m hkm hdisj hcov hJne
  have hK0nn : 0 ≤ K0 * R ^ 2 := by rw [hK0]; positivity
  have hfin : ((m - k : ℕ) : ℝ) * (K0 * R ^ 2) ≤ n * (K0 * R ^ 2) :=
    mul_le_mul_of_nonneg_right hcard hK0nn
  rw [← Finset.mul_sum, ← hPs', ← hin] at hsum
  unfold Fc
  nlinarith

lemma cgd2_limit (A B ρ K η0 : ℝ) (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (hη0 : 0 < η0)
    (h : ∀ η, 0 < η → η < η0 → A ≤ B + K * (ρ + η) ^ 2) : A ≤ B + K * ρ ^ 2 := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  set η := min (η0 / 2) (min 1 (ε / (K * (2 * ρ + 1) + 1))) with hη
  have hpos : 0 < η := by
    rw [hη]; apply lt_min (by linarith) (lt_min one_pos (by positivity))
  have h1 : η ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have h2 : η ≤ ε / (K * (2 * ρ + 1) + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
  have h3 : η < η0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hA := h η hpos h3
  have hD : 0 < K * (2 * ρ + 1) + 1 := by positivity
  have h4 : η * (K * (2 * ρ + 1) + 1) ≤ ε := by rwa [le_div_iff₀ hD] at h2
  have h5 : K * (ρ + η) ^ 2 ≤ K * ρ ^ 2 + η * (K * (2 * ρ + 1)) := by
    have : (ρ + η) ^ 2 ≤ ρ ^ 2 + η * (2 * ρ + 1) := by nlinarith
    nlinarith
  nlinarith

lemma cgd2_rlin {n : ℕ} (s : ℕ → Vec n) (i0 : ℕ) (C ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ j, ‖s (i0 + j + 1) - s (i0 + j)‖ ≤ C * ρ ^ j) : RLinear s := by
  set s' : ℕ → Vec n := fun j => s (i0 + j) with hs'
  have hd : ∀ j, dist (s' j) (s' (j + 1)) ≤ C * ρ ^ j := by
    intro j; rw [dist_eq_norm, norm_sub_rev]; simp only [hs']; rw [← add_assoc]; exact h j
  have hcau := cauchySeq_of_le_geometric ρ C hρ1 hd
  obtain ⟨xinf, hlim⟩ := cauchySeq_tendsto_of_complete hcau
  have hbd := dist_le_of_le_geometric_of_tendsto ρ C hρ1 hd hlim
  set ρ' := max ρ (1 / 2) with hρ'
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ'1 : ρ' < 1 := max_lt hρ1 (by norm_num)
  set A := C / (1 - ρ) with hA
  set M0 := ∑ i ∈ Finset.range i0, ‖s i - xinf‖ with hM0
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨xinf, (|A| + M0) / ρ' ^ i0, ρ', hρ'0.le, hρ'1, ?_⟩
  intro i
  have hpi0 : 0 < ρ' ^ i0 := pow_pos hρ'0 _
  by_cases hi : i0 ≤ i
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    have h1 := hbd j
    rw [dist_eq_norm] at h1
    simp only [hs'] at h1
    have h2 : C * ρ ^ j / (1 - ρ) ≤ |A| * ρ' ^ j := by
      rw [hA, mul_comm C, mul_div_assoc, mul_comm]
      apply mul_le_mul (le_abs_self _) (pow_le_pow_left₀ hρ0 (le_max_left _ _) _)
        (pow_nonneg hρ0 _) (abs_nonneg _)
    have h3 : |A| * ρ' ^ j ≤ (|A| + M0) / ρ' ^ i0 * ρ' ^ (i0 + j) := by
      rw [pow_add, div_mul_eq_mul_div, mul_comm (ρ' ^ i0), ← mul_assoc, mul_div_assoc,
        div_self hpi0.ne', mul_one]
      exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hρ'0.le _)
    linarith
  · push Not at hi
    have h1 : ‖s i - xinf‖ ≤ M0 :=
      Finset.single_le_sum (f := fun i => ‖s i - xinf‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr hi)
    have h2 : ρ' ^ i0 ≤ ρ' ^ i := pow_le_pow_of_le_one hρ'0.le hρ'1.le hi.le
    have h3 : M0 ≤ (|A| + M0) / ρ' ^ i0 * ρ' ^ i := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi0]
      nlinarith [abs_nonneg A, pow_nonneg hρ'0.le i]
    linarith

lemma cgd2_qlin (s : ℕ → ℝ) (v q : ℝ) (i0 : ℕ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hlow : ∀ i, v ≤ s i) (hstep : ∀ i, i0 ≤ i → s (i + 1) - v ≤ q * (s i - v)) : QLinear s := by
  refine ⟨v, ?_, q, hq0, hq1, ?_⟩
  · have hgeo : ∀ j, s (i0 + j) - v ≤ q ^ j * (s i0 - v) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc s (i0 + (j + 1)) - v = s (i0 + j + 1) - v := by rw [add_assoc]
          _ ≤ q * (s (i0 + j) - v) := hstep _ (by omega)
          _ ≤ q * (q ^ j * (s i0 - v)) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ (j + 1) * (s i0 - v) := by ring
    rw [← Filter.tendsto_add_atTop_iff_nat i0]
    have hlim : Tendsto (fun j => v + q ^ j * (s i0 - v)) atTop (𝓝 (v + 0 * (s i0 - v))) :=
      tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _)
    rw [zero_mul, add_zero] at hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    · intro j; simp only; rw [add_comm j]; exact hlow _
    · intro j; simp only; rw [add_comm j]; linarith [hgeo j]
  · filter_upwards [Filter.eventually_ge_atTop i0] with i hi
    rw [abs_of_nonneg (by linarith [hlow (i + 1)]), abs_of_nonneg (by linarith [hlow i])]
    exact hstep i hi

theorem solution {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → TsengCGD.Global.Vec n) (α : ℕ → ℝ) (hrun : TsengCGD.Global.IsCGDRun f D P c J H x d α)
    (lam lamBar : ℝ) (hA1 : TsengCGD.Global.Assumption1 H lam lamBar)
    (L : ℝ) (hL : GradLipOn f D L)
    (t : ℕ → ℕ) (hRGS : RestrictedGaussSeidel J t)
    (hA2a : Assumption2a f D P c) (hA2b : Assumption2b f D P c)
    (hsep : ∀ k, TsengCGD.Global.BlockSeparable D P (J k))
    (β σ γ : ℝ) (αinit : ℕ → ℝ) (harm : TsengCGD.Global.IsArmijo f D P c β σ γ αinit H x d α)
    (hinit1 : ∀ k, αinit k ≤ 1) (hinit : ∃ a > 0, ∀ k, a ≤ αinit k) :
    (Antitone (fun k => TsengCGD.Global.Fc f P c (x k)) ∧ Tendsto (fun k => TsengCGD.Global.Fc f P c (x k)) atTop atBot) ∨
      (QLinear (fun i => TsengCGD.Global.Fc f P c (x (t i))) ∧ RLinear (fun i => x (t i))) := by
  have hpar := harm.1
  have hα0 : ∀ k, 0 < α k := hrun.step_pos
  have hα1 : ∀ k, α k ≤ 1 := by
    intro k; obtain ⟨j, hj, -, -⟩ := harm.2.2 k
    rw [hj]
    have hb : β ^ j ≤ 1 := pow_le_one₀ hpar.beta_pos.le hpar.beta_lt_one.le
    have hb0 : 0 ≤ β ^ j := pow_nonneg hpar.beta_pos.le _
    nlinarith [harm.2.1 k, hinit1 k]
  have h1a := TsengCGD.Global.theorem1_a f D P c hs J H x d α αinit β σ γ lam lamBar hrun harm hA1
    (by obtain ⟨a, ha, h⟩ := hinit; exact ⟨a, ha, h⟩)
  obtain ⟨hanti, -, hqf, hdesc⟩ := h1a
  by_cases hbdd : BddBelow (Set.range fun k => Fc f P c (x k))
  swap
  · left; refine ⟨hanti, ?_⟩
    rw [Filter.tendsto_atBot]; intro b
    have : ∃ k, Fc f P c (x k) < b := by
      by_contra hc; push Not at hc; exact hbdd ⟨b, by rintro _ ⟨k, rfl⟩; exact hc k⟩
    obtain ⟨k, hk⟩ := this
    filter_upwards [Filter.eventually_ge_atTop k] with k' hk'
    exact le_trans (hanti hk') hk.le
  right
  obtain ⟨⟨a, ha, hαa⟩, h1f⟩ := theorem1_f f D P c hs J H x d α hrun lam lamBar hA1 β σ γ αinit
    harm hinit L hL
  obtain ⟨-, hdlim⟩ := h1f hbdd
  obtain ⟨C, hC, h2a⟩ := theorem2_a (n := n) L lam lamBar
  have hdI : ∀ i, ‖dI f D P c (x (t i))‖ ≤ C * r t d i := by
    intro i
    have := h2a f D P c J H x d α t hs hL hrun hrun.iterate_mem hA1 hRGS hsep 1 hα1 i
    simpa using this
  obtain ⟨hmono, ht0, hcyc⟩ := hRGS
  have hkm : ∀ i, t i ≤ t (i + 1) := fun i => (hmono (Nat.lt_succ_self i)).le
  have hcardi : ∀ i, t (i + 1) - t i ≤ n := fun i =>
    cgd2_card J (t i) (t (i + 1)) (hkm i) (hcyc i).1 (hcyc i).2 hrun.J_nonempty
  have hr0 : ∀ i, 0 ≤ r t d i := fun i => Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hrlim : Tendsto (fun i => r t d i) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]; intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hdlim) (ε / (n + 1)) (by positivity)
    refine ⟨N, fun i hi => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hr0 i)]
    have hb : ∀ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖ ≤ ε / (n + 1) := by
      intro ℓ hℓ
      have hNl : N ≤ ℓ := le_trans hi (le_trans (hmono.id_le i) (Finset.mem_Ico.mp hℓ).1)
      have := hN ℓ hNl; rw [dist_zero_right] at this; exact this.le
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    calc r t d i ≤ ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ε / (n + 1) := Finset.sum_le_sum hb
      _ = ((t (i + 1) - t i : ℕ) : ℝ) * (ε / (n + 1)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ n * (ε / (n + 1)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcardi i) (by positivity)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hn1]; nlinarith
  have hdist_i : ∀ i, ‖x (t (i + 1)) - x (t i)‖ ≤ r t d i := fun i =>
    cgd2_dist x d α (t i) hrun.step hα0 hα1 (t (i + 1)) (hkm i)
  obtain ⟨hXne, hEB⟩ := hA2a
  obtain ⟨τ, hτ, ε, hε, hEBζ⟩ := hEB (Fc f P c (x 0))
  obtain ⟨δ, hδ, hsepδ⟩ := hA2b
  have hev : ∀ᶠ i in atTop, C * r t d i ≤ ε ∧ (τ * C + 1) * r t d i < δ / 4 := by
    have h1 : Tendsto (fun i => C * r t d i) atTop (𝓝 0) := by simpa using hrlim.const_mul C
    have h2 : Tendsto (fun i => (τ * C + 1) * r t d i) atTop (𝓝 0) := by
      simpa using hrlim.const_mul (τ * C + 1)
    exact (h1.eventually (ge_mem_nhds hε)).and (h2.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨i0, hi0⟩ := Filter.eventually_atTop.mp hev
  have hFanti : ∀ k, Fc f P c (x k) ≤ Fc f P c (x 0) := fun k => hanti (Nat.zero_le k)
  have hnear : ∀ i, i0 ≤ i → ∀ η > 0, ∃ xb ∈ statSet f D P c,
      ‖x (t i) - xb‖ < τ * C * r t d i + η := by
    intro i hi η hη
    have hid := hEBζ (x (t i)) (hrun.iterate_mem _) (hFanti _) (le_trans (hdI i) (hi0 i hi).1)
    have : Metric.infDist (x (t i)) (statSet f D P c) < τ * C * r t d i + η := by
      calc _ ≤ τ * ‖dI f D P c (x (t i))‖ := hid
        _ ≤ τ * (C * r t d i) := mul_le_mul_of_nonneg_left (hdI i) hτ.le
        _ < _ := by rw [← mul_assoc]; linarith
    obtain ⟨xb, hxb, hdist⟩ := (Metric.infDist_lt_iff hXne).mp this
    exact ⟨xb, hxb, by rwa [dist_eq_norm] at hdist⟩
  have hexists : ∀ i, i0 ≤ i → ∃ xb ∈ statSet f D P c, ‖x (t i) - xb‖ < δ / 4 := by
    intro i hi
    have h := (hi0 i hi).2
    have hr := hr0 i
    obtain ⟨xb, hxb, hd⟩ := hnear i hi (δ / 4 - τ * C * r t d i) (by nlinarith)
    exact ⟨xb, hxb, by linarith⟩
  have hsame : ∀ xb ∈ statSet f D P c, ∀ xb' ∈ statSet f D P c, ‖xb - xb'‖ < δ →
      Fc f P c xb = Fc f P c xb' := by
    intro xb hxb xb' hxb' hlt
    by_contra hne
    have := hsepδ xb hxb xb' hxb' hne
    linarith
  obtain ⟨xb0, hxb0, hxb0d⟩ := hexists i0 le_rfl
  set vb := Fc f P c xb0 with hvb
  have hv : ∀ i, i0 ≤ i → ∀ xb ∈ statSet f D P c, ‖x (t i) - xb‖ < δ / 4 → Fc f P c xb = vb := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base =>
      intro xb hxb hd
      apply hsame xb hxb xb0 hxb0
      calc ‖xb - xb0‖ ≤ ‖xb - x (t i0)‖ + ‖x (t i0) - xb0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < δ := by rw [norm_sub_rev]; linarith
    | succ i hi ih =>
      intro xb hxb hd
      obtain ⟨xb', hxb', hd'⟩ := hexists i hi
      rw [← ih xb' hxb' hd']
      apply hsame xb hxb xb' hxb'
      have h1 := hdist_i i
      have h2 := (hi0 i hi).2
      have h3 : r t d i ≤ (τ * C + 1) * r t d i := by nlinarith [hr0 i, mul_pos hτ hC]
      calc ‖xb - xb'‖ ≤ ‖xb - x (t (i + 1))‖ + ‖x (t (i + 1)) - xb'‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖xb - x (t (i + 1))‖ + (‖x (t (i + 1)) - x (t i)‖ + ‖x (t i) - xb'‖) := by
            gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < δ := by rw [norm_sub_rev xb]; linarith
  obtain ⟨U, hU, hDU, hf⟩ := hs.smooth
  have hDc : Convex ℝ D := hs.properConvexLsc.2.1
  -- lower bound (38)
  have hlowi : ∀ i, i0 ≤ i → vb ≤ Fc f P c (x (t i)) + L * (τ * C * r t d i) ^ 2 := by
    intro i hi
    have h2 := (hi0 i hi).2
    have hr := hr0 i
    have hρ : 0 ≤ τ * C * r t d i := by positivity
    apply cgd2_limit _ _ _ _ (δ / 4 - τ * C * r t d i) hL.1 hρ (by nlinarith)
    intro η hη hηlt
    obtain ⟨xb, hxb, hd⟩ := hnear i hi η hη
    have hvx := hv i hi xb hxb (by linarith)
    have hxbD : xb ∈ D := hxb.1
    have hVI := cgd2_VI f D P c hs xb hxb (x (t i)) (hrun.iterate_mem _)
    have htay := cgd2_taylor f D U hU hDU hf hDc L hL xb (x (t i)) hxbD (hrun.iterate_mem _)
    have hsq : ‖x (t i) - xb‖ ^ 2 ≤ (τ * C * r t d i + η) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hd.le 2
    have := (abs_le.mp htay).1
    rw [← hvx]; unfold Fc
    nlinarith [mul_le_mul_of_nonneg_left hsq hL.1]
  have hlow : ∀ k, vb ≤ Fc f P c (x k) := by
    intro k
    by_contra hcon
    push Not at hcon
    have hρlim : Tendsto (fun i => L * (τ * C * r t d i) ^ 2) atTop (𝓝 0) := by
      have := ((hrlim.const_mul (τ * C)).pow 2).const_mul L
      simpa using this
    obtain ⟨i1, hi1⟩ := Filter.eventually_atTop.mp
      (hρlim.eventually (gt_mem_nhds (show (0:ℝ) < vb - Fc f P c (x k) by linarith)))
    set i := max i0 (max i1 k)
    have h1 := hlowi i (le_max_left _ _)
    have h2 := hi1 i (le_trans (le_max_left _ _) (le_max_right _ _))
    have h3 : k ≤ t i := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hmono.id_le i)
    have h4 := hanti h3
    simp only at h4
    linarith
  -- block witnesses
  have hsep' : ∀ k, ∃ DJ PJ DJC PJC, IsBlockSepWitness D P (J k) DJ PJ DJC PJC := hsep
  choose DJ PJ DJC PJC hw using hsep'
  obtain ⟨hlam, hlamle, hA⟩ := hA1
  set Kc := L + n * ((L ^ 2 + 1) / 2 + lamBar) with hKc
  have hKc0 : 0 ≤ Kc := by
    have := hL.1; have : 0 ≤ lamBar := by linarith
    positivity
  set Bc : ℕ → ℝ := fun i => ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), (α ℓ - 1) * ((1 - γ) * qf (H ℓ) (d ℓ) +
          Delta f P c γ (H ℓ) (x ℓ) (d ℓ)) with hBc
  -- upper bound (40)
  have hup : ∀ i, i0 ≤ i → Fc f P c (x (t (i + 1))) - vb ≤
      Bc i + Kc * ((τ * C + 1) * r t d i) ^ 2 := by
    intro i hi
    have h2 := (hi0 i hi).2
    have hr := hr0 i
    have hρ : 0 ≤ (τ * C + 1) * r t d i := by positivity
    apply cgd2_limit _ _ _ _ (δ / 4 - τ * C * r t d i) hKc0 hρ (by nlinarith)
    intro η hη hηlt
    obtain ⟨xb, hxb, hd⟩ := hnear i hi η hη
    have hvx := hv i hi xb hxb (by linarith)
    have hcy := cgd2_cycle f D P c hs J H x d α hrun.iterate_mem hrun.J_nonempty hrun.H_posDef
      hrun.dir hrun.step hα0 hα1 lam lamBar ⟨hlam, hlamle, hA⟩ L hL γ hpar.gamma_nonneg
      hpar.gamma_lt_one DJ PJ DJC PJC hw (t i) (t (i + 1)) (hkm i) (hcyc i).1 (hcyc i).2 xb hxb.1
    have hsq : (‖x (t i) - xb‖ + r t d i) ^ 2 ≤ ((τ * C + 1) * r t d i + η) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); nlinarith
    rw [← hvx]
    have : Kc * (‖x (t i) - xb‖ + r t d i) ^ 2 ≤ Kc * ((τ * C + 1) * r t d i + η) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hKc0
    have hcy' : Fc f P c (x (t (i + 1))) - Fc f P c xb ≤
        Kc * (‖x (t i) - xb‖ + r t d i) ^ 2 + Bc i := hcy
    linarith
  -- per-iteration facts
  have hγ1 := hpar.gamma_lt_one
  set W := (1 - γ) * lam with hW
  have hWpos : 0 < W := by rw [hW]; nlinarith
  have hDn : ∀ ℓ, W * ‖d ℓ‖ ^ 2 ≤ -Delta f P c γ (H ℓ) (x ℓ) (d ℓ) := by
    intro ℓ; have := hqf ℓ; simp only at this; rw [hW]; nlinarith
  have hDle : ∀ ℓ, Delta f P c γ (H ℓ) (x ℓ) (d ℓ) ≤ 0 := by
    intro ℓ; have := hDn ℓ; nlinarith [sq_nonneg ‖d ℓ‖]
  have hBterm : ∀ ℓ, (α ℓ - 1) * ((1 - γ) * qf (H ℓ) (d ℓ) + Delta f P c γ (H ℓ) (x ℓ) (d ℓ)) ≤
      -Delta f P c γ (H ℓ) (x ℓ) (d ℓ) := by
    intro ℓ
    have h1 := hqf ℓ; simp only at h1
    have hq0 : 0 ≤ (1 - γ) * qf (H ℓ) (d ℓ) := by
      have : 0 ≤ (1 - γ) * lam * ‖d ℓ‖ ^ 2 := by nlinarith [sq_nonneg ‖d ℓ‖]
      linarith [h1.2]
    have := hα0 ℓ; have := hα1 ℓ
    nlinarith [h1.1]
  set S : ℕ → ℝ := fun i => ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), -Delta f P c γ (H ℓ) (x ℓ) (d ℓ)
    with hS
  have hBS : ∀ i, Bc i ≤ S i := fun i => Finset.sum_le_sum (fun ℓ _ => hBterm ℓ)
  have hrS : ∀ i, W * r t d i ^ 2 ≤ n * S i := by
    intro i
    have h1 : r t d i ^ 2 ≤ ((Finset.Ico (t i) (t (i + 1))).card : ℝ) *
        ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    rw [Nat.card_Ico] at h1
    have h2 : W * ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖ ^ 2 ≤ S i := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun ℓ _ => hDn ℓ)
    have h3 : (((t (i + 1) - t i : ℕ)) : ℝ) ≤ n := by exact_mod_cast hcardi i
    have h4 : 0 ≤ ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have h5 : 0 ≤ S i := le_trans (mul_nonneg hWpos.le h4) h2
    calc W * r t d i ^ 2 ≤ W * (((t (i + 1) - t i : ℕ) : ℝ) *
          ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hWpos.le
      _ ≤ W * (n * ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h4) hWpos.le
      _ = n * (W * ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖ ^ 2) := by ring
      _ ≤ n * S i := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have hσ := hpar.sigma_pos
  have hdesS : ∀ i, σ * a * S i ≤ Fc f P c (x (t i)) - Fc f P c (x (t (i + 1))) := by
    intro i
    have key : ∀ q, t i ≤ q → σ * a * ∑ ℓ ∈ Finset.Ico (t i) q,
        -Delta f P c γ (H ℓ) (x ℓ) (d ℓ) ≤ Fc f P c (x (t i)) - Fc f P c (x q) := by
      intro q hq
      induction q, hq using Nat.le_induction with
      | base => simp
      | succ q hq ih =>
        rw [Finset.sum_Ico_succ_top hq, mul_add]
        have h1 := (hdesc q).1; simp only at h1
        have h2 := hDle q
        have h3 : σ * a * -Delta f P c γ (H q) (x q) (d q) ≤
            σ * α q * -Delta f P c γ (H q) (x q) (d q) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left (hαa q) hσ.le
        linarith
    exact key (t (i + 1)) (hkm i)
  set E := Kc * (τ * C + 1) ^ 2 * n + W with hE
  set G := σ * a * W with hG
  have hEpos : 0 < E := by rw [hE]; have : 0 ≤ Kc * (τ * C + 1) ^ 2 * n := by positivity
                           linarith
  have hGpos : 0 < G := by rw [hG]; positivity
  have hSnn : ∀ i, 0 ≤ S i := fun i => Finset.sum_nonneg (fun ℓ _ => by linarith [hDle ℓ])
  have hkey : ∀ i, i0 ≤ i → (G + E) * (Fc f P c (x (t (i + 1))) - vb) ≤
      E * (Fc f P c (x (t i)) - vb) := by
    intro i hi
    have h1 := hup i hi
    have h2 := hBS i
    have h3 := hrS i
    have h4 := hdesS i
    have h5 : W * (Fc f P c (x (t (i + 1))) - vb) ≤ E * S i := by
      have : W * (Fc f P c (x (t (i + 1))) - vb) ≤ W * (S i + Kc * ((τ * C + 1) * r t d i) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hWpos.le
      have h6 : Kc * (τ * C + 1) ^ 2 * (W * r t d i ^ 2) ≤ Kc * (τ * C + 1) ^ 2 * (n * S i) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have e1 : W * (S i + Kc * ((τ * C + 1) * r t d i) ^ 2) =
          W * S i + Kc * (τ * C + 1) ^ 2 * (W * r t d i ^ 2) := by ring
      have e2 : E * S i = Kc * (τ * C + 1) ^ 2 * (n * S i) + W * S i := by rw [hE]; ring
      linarith
    have h7 : σ * a * (W * (Fc f P c (x (t (i + 1))) - vb)) ≤ σ * a * (E * S i) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have h8 : E * (σ * a * S i) ≤ E * (Fc f P c (x (t i)) - Fc f P c (x (t (i + 1)))) :=
      mul_le_mul_of_nonneg_left h4 hEpos.le
    have e1 : (G + E) * (Fc f P c (x (t (i + 1))) - vb) =
        σ * a * (W * (Fc f P c (x (t (i + 1))) - vb)) + E * (Fc f P c (x (t (i + 1))) - vb) := by
      rw [hG]; ring
    have e2 : σ * a * (E * S i) = E * (σ * a * S i) := by ring
    have e3 : E * (Fc f P c (x (t i)) - Fc f P c (x (t (i + 1)))) =
        E * (Fc f P c (x (t i)) - vb) - E * (Fc f P c (x (t (i + 1))) - vb) := by ring
    linarith
  set q := E / (G + E) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  have hstepq : ∀ i, i0 ≤ i → Fc f P c (x (t (i + 1))) - vb ≤ q * (Fc f P c (x (t i)) - vb) := by
    intro i hi
    rw [hq, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith [hkey i hi]
  refine ⟨cgd2_qlin _ vb q i0 hq0 hq1 (fun i => hlow (t i)) hstepq, ?_⟩
  -- R-linear
  have hgeo : ∀ j, Fc f P c (x (t (i0 + j))) - vb ≤ q ^ j * (Fc f P c (x (t i0)) - vb) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc Fc f P c (x (t (i0 + (j + 1)))) - vb = Fc f P c (x (t (i0 + j + 1))) - vb := by
            rw [add_assoc]
        _ ≤ q * (Fc f P c (x (t (i0 + j))) - vb) := hstepq _ (by omega)
        _ ≤ q * (q ^ j * (Fc f P c (x (t i0)) - vb)) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (j + 1) * (Fc f P c (x (t i0)) - vb) := by ring
  have hrsq : ∀ i, G * r t d i ^ 2 ≤ n * (Fc f P c (x (t i)) - vb) := by
    intro i
    have h3 := hrS i
    have h4 := hdesS i
    have h5 := hlow (t (i + 1))
    have h6 : σ * a * (W * r t d i ^ 2) ≤ σ * a * (n * S i) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h7 : (n : ℝ) * (σ * a * S i) ≤ n * (Fc f P c (x (t i)) - Fc f P c (x (t (i + 1)))) :=
      mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
    have h8 : (n : ℝ) * (Fc f P c (x (t i)) - Fc f P c (x (t (i + 1)))) ≤
        n * (Fc f P c (x (t i)) - vb) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have e1 : G * r t d i ^ 2 = σ * a * (W * r t d i ^ 2) := by rw [hG]; ring
    have e2 : σ * a * (n * S i) = (n : ℝ) * (σ * a * S i) := by ring
    linarith
  set u0 := Fc f P c (x (t i0)) - vb with hu0
  apply cgd2_rlin (fun i => x (t i)) i0 (Real.sqrt (n * u0 / G)) (Real.sqrt q)
    (Real.sqrt_nonneg _) (by rw [Real.sqrt_lt' one_pos]; simpa using hq1)
  intro j
  have h1 := hdist_i (i0 + j)
  have h2 := hrsq (i0 + j)
  have h3 := hgeo j
  have h4 : r t d (i0 + j) ^ 2 ≤ n * u0 / G * q ^ j := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hGpos]
    have : (n : ℝ) * (Fc f P c (x (t (i0 + j))) - vb) ≤ n * (q ^ j * u0) :=
      mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    have e : (n : ℝ) * (q ^ j * u0) = n * u0 * q ^ j := by ring
    have e2 : r t d (i0 + j) ^ 2 * G = G * r t d (i0 + j) ^ 2 := by ring
    linarith
  have h5 : r t d (i0 + j) ≤ Real.sqrt (n * u0 / G * q ^ j) := by
    rw [← Real.sqrt_sq (hr0 (i0 + j))]; exact Real.sqrt_le_sqrt h4
  have hu0nn : 0 ≤ u0 := by rw [hu0]; linarith [hlow (t i0)]
  have h6 : Real.sqrt (n * u0 / G * q ^ j) = Real.sqrt (n * u0 / G) * Real.sqrt q ^ j := by
    rw [Real.sqrt_mul (by positivity)]
    congr 1
    rw [show q ^ j = (Real.sqrt q ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hq0]]
    exact Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)
  linarith

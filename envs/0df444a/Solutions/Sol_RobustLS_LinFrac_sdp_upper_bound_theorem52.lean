-- Prove2me | solution 1 for RobustLS.LinFrac.sdp_upper_bound_theorem52
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T03:20:16.765449+00:00
-- url     : https://prove2.me/submissions/2fdfea86-91d8-4899-9267-4de560e5f313

-- Licensed under Apache 2.0. Full exact theorem: Robust linear-fractional least squares corrected Theorem 5.2.
import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix


open Matrix BigOperators

namespace RobustLFTProof

variable {ι : Type*} [Fintype ι]

noncomputable def qform (F : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ F *ᵥ v

def outer (v : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i * v j

def pairing (F W : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, F i j * W i j

lemma qform_eq_pairing (F : Matrix ι ι ℝ) (v : ι → ℝ) :
    qform F v = pairing F (outer v) := by
  simp only [qform, dotProduct, mulVec, pairing, outer, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma pairing_add (F W Z : Matrix ι ι ℝ) : pairing F (W + Z) = pairing F W + pairing F Z := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

lemma pairing_sum (F : Matrix ι ι ℝ) (l : List (Matrix ι ι ℝ)) :
    pairing F l.sum = (l.map (pairing F)).sum := by
  induction l with
  | nil => simp [pairing]
  | cons a l ih => simp [pairing_add, ih]

lemma qform_zero (F : Matrix ι ι ℝ) : qform F 0 = 0 := by simp [qform]

lemma continuous_qform (F : Matrix ι ι ℝ) : Continuous (qform F) := by
  unfold qform dotProduct mulVec
  fun_prop

omit [Fintype ι] in
lemma outer_rotate (a b : ι → ℝ) (c s : ℝ) (h : c^2+s^2=1) :
    outer (c • a + s • b) + outer ((-s) • a + c • b) = outer a + outer b := by
  ext i j
  simp only [outer, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply]
  calc
    _ = (c^2+s^2) * (a i*a j+b i*b j) := by ring
    _ = _ := by rw [h, one_mul]

lemma qform_rotate (F : Matrix ι ι ℝ) (a b : ι → ℝ) (c s : ℝ) (h : c^2+s^2=1) :
    qform F (c • a+s • b)+qform F ((-s) • a+c • b) = qform F a+qform F b := by
  simp only [qform_eq_pairing]
  rw [← pairing_add, outer_rotate a b c s h, pairing_add]

end RobustLFTProof


open Matrix Set

namespace RobustLFTProof

variable {ι : Type*} [Fintype ι]

lemma rotate_to_zero (H : Matrix ι ι ℝ) (a b : ι → ℝ)
    (ha : qform H a < 0) (hb : 0 < qform H b) :
    ∃ c d : ι → ℝ, qform H c = 0 ∧
      outer c + outer d = outer a + outer b ∧
      qform H d = qform H a + qform H b := by
  let f : ℝ → ℝ := fun t => qform H (Real.cos t • a + Real.sin t • b)
  have hf : Continuous f := by dsimp [f]; exact (continuous_qform H).comp (by fun_prop)
  have h0 : f 0 < 0 := by simpa [f] using ha
  have h1 : 0 < f (Real.pi/2) := by simpa [f] using hb
  obtain ⟨t,_,ht⟩ := intermediate_value_Icc (by positivity : (0:ℝ) ≤ Real.pi/2)
    hf.continuousOn (show 0 ∈ Icc (f 0) (f (Real.pi/2)) from ⟨h0.le,h1.le⟩)
  have hcs : (Real.cos t)^2+(Real.sin t)^2=1 := by nlinarith [Real.sin_sq_add_cos_sq t]
  refine ⟨Real.cos t • a+Real.sin t • b, (-Real.sin t) • a+Real.cos t • b, ht, ?_, ?_⟩
  · exact outer_rotate a b _ _ hcs
  · have h := qform_rotate H a b _ _ hcs
    change qform H (Real.cos t • a+Real.sin t • b)=0 at ht
    linarith

private lemma list_sum_nonpos {l : List ℝ} (h : ∀ a ∈ l, a ≤ 0) : l.sum ≤ 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons]
    exact add_nonpos (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma constrained_list_decomposition (H : Matrix ι ι ℝ) (l : List (ι → ℝ))
    (hs : 0 ≤ (l.map (qform H)).sum) :
    ∃ k : List (ι → ℝ), (k.map outer).sum = (l.map outer).sum ∧
      ∀ v ∈ k, 0 ≤ qform H v := by
  classical
  generalize hn : l.length = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hall : ∀ v ∈ l, 0 ≤ qform H v
    · exact ⟨l,rfl,hall⟩
    push Not at hall
    obtain ⟨a,ha,hqa⟩ := hall
    let l₁ := l.erase a
    have hp₁ : l.Perm (a::l₁) := List.perm_cons_erase ha
    have he₁ := (hp₁.map (qform H)).sum_eq
    have hex : ∃ b ∈ l₁, 0 < qform H b := by
      by_contra! hb
      have hz : (l₁.map (qform H)).sum ≤ 0 := by
        apply list_sum_nonpos
        intro x hx
        obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
        exact hb v hv
      simp only [List.map_cons,List.sum_cons] at he₁
      linarith
    obtain ⟨b,hb,hqb⟩ := hex
    let l₂ := l₁.erase b
    have hp₂ : l₁.Perm (b::l₂) := List.perm_cons_erase hb
    obtain ⟨c,d,hc,hcd,hqd⟩ := rotate_to_zero H a b hqa hqb
    have hperm : l.Perm (a::b::l₂) := hp₁.trans (List.Perm.cons a hp₂)
    have hsum := (hperm.map (qform H)).sum_eq
    have hlen := hperm.length_eq
    have hsmall : (d::l₂).length < n := by simp only [List.length_cons] at hlen ⊢; omega
    have hnonneg : 0 ≤ ((d::l₂).map (qform H)).sum := by
      simp only [List.map_cons,List.sum_cons] at hsum ⊢
      rw [hqd]
      linarith
    obtain ⟨k,hk,hkpos⟩ := ih _ hsmall (d::l₂) hnonneg rfl
    refine ⟨c::k,?_,?_⟩
    · have ho := (hperm.map outer).sum_eq
      simp only [List.map_cons,List.sum_cons] at ho ⊢
      rw [hk]
      simp only [List.map_cons,List.sum_cons]
      rw [← add_assoc,hcd,add_assoc]
      exact ho.symm
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hc.ge
      · exact hkpos v hv

end RobustLFTProof


open Matrix Set Topology

namespace RobustLFTProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def positiveCone : Set (Matrix ι ι ℝ) :=
  {F | ∀ v : ι → ℝ, v ≠ 0 → 0 < qform F v}

omit [DecidableEq ι] in
lemma qform_smul_vec (F : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) :
    qform F (c • v) = c^2*qform F v := by
  simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

omit [DecidableEq ι] in
lemma qform_add_matrix (F G : Matrix ι ι ℝ) (v : ι → ℝ) :
    qform (F+G) v = qform F v+qform G v := by simp [qform, add_mulVec, dotProduct_add]

omit [DecidableEq ι] in
lemma qform_smul_matrix (F : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) :
    qform (c • F) v = c*qform F v := by simp [qform, smul_mulVec, dotProduct_smul]

omit [DecidableEq ι] in
lemma positiveCone_convex : Convex ℝ (positiveCone (ι := ι)) := by
  intro F hF G hG a b ha hb hab v hv
  rw [qform_add_matrix,qform_smul_matrix,qform_smul_matrix]
  have hfv := hF v hv
  have hgv := hG v hv
  rcases lt_or_eq_of_le ha with ha | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hfv) (mul_nonneg hb hgv.le)
  · simp only [zero_add] at hab
    simp [hab,hgv]

omit [DecidableEq ι] in
lemma positiveCone_iff_sphere (F : Matrix ι ι ℝ) : F ∈ positiveCone ↔
    ∀ v : ι → ℝ, ‖v‖ = 1 → 0 < qform F v := by
  constructor
  · intro h v hv; exact h v (by intro he; simp [he] at hv)
  · intro h v hv
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hp := h _ hu
    rw [qform_smul_vec] at hp
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (inv_pos.mpr hn))).mp hp

omit [DecidableEq ι] in
lemma positiveCone_isOpen : IsOpen (positiveCone (ι := ι)) := by
  let S : Set (ι → ℝ) := {v | ‖v‖ = 1}
  have hs : IsCompact S := by
    simpa only [S,Metric.sphere,dist_zero_right] using isCompact_sphere (0 : ι → ℝ) 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp hs
  have hc : Continuous (fun p : Matrix ι ι ℝ × S => qform p.1 p.2.val) := by
    simp only [qform, mulVec, dotProduct]
    apply continuous_finsetSum
    intro i _
    apply Continuous.mul
    · exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    · apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
  have hz : IsClosed (Prod.fst '' {p : Matrix ι ι ℝ × S | qform p.1 p.2.val ≤ 0}) :=
    isClosedMap_fst_of_compactSpace _ (isClosed_le hc continuous_const)
  have he : positiveCone (ι := ι) =
      (Prod.fst '' {p : Matrix ι ι ℝ × S | qform p.1 p.2.val ≤ 0})ᶜ := by
    ext F
    rw [positiveCone_iff_sphere]
    simp only [mem_compl_iff,mem_image,mem_ofPred_eq,Prod.exists,exists_and_right,exists_eq_right]
    constructor
    · intro h ⟨v,hv⟩; exact (h v v.property).not_ge hv
    · intro h v hv
      by_contra! hn
      exact h ⟨⟨v,hv⟩,hn⟩
  rw [he]
  exact hz.isOpen_compl

lemma one_mem_positiveCone : (1 : Matrix ι ι ℝ) ∈ positiveCone := by
  intro v hv
  simpa [qform] using (dotProduct_self_star_pos_iff.mpr hv : 0 < v ⬝ᵥ star v)

omit [DecidableEq ι] in
lemma positiveCone_smul {F : Matrix ι ι ℝ} (hF : F ∈ positiveCone) {a : ℝ} (ha : 0 < a) :
    a • F ∈ positiveCone := by
  intro v hv
  rw [qform_smul_matrix]
  exact mul_pos ha (hF v hv)

omit [DecidableEq ι] in
lemma posDef_iff_positiveCone {F : Matrix ι ι ℝ} (hF : F.IsHermitian) :
    F.PosDef ↔ F ∈ positiveCone := by
  rw [posDef_iff_dotProduct_mulVec]
  simp only [star_trivial,hF,true_and,positiveCone,mem_ofPred_eq,qform]

end RobustLFTProof


open Matrix BigOperators
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace RobustLFTProof
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma positive_outer_decomposition (W : Matrix ι ι ℝ) (hW : W.PosSemidef) :
    ∃ l : List (ι → ℝ), (l.map outer).sum = W := by
  classical
  let B := CFC.sqrt W
  have hb : B.transpose = B := by
    ext i j
    simpa [B] using congrFun (congrFun (CFC.sqrt_nonneg W).posSemidef.isHermitian i) j
  have he : (∑ k, outer (fun i => B i k)) = W := by
    calc
      _ = B * B.transpose := by
        ext i j
        simp [Matrix.sum_apply, outer, Matrix.mul_apply, Matrix.transpose_apply]
      _ = W := by rw [hb]; exact CFC.sqrt_mul_sqrt_self W hW.nonneg
  refine ⟨(Finset.univ.toList.map (fun k => fun i => B i k)), ?_⟩
  rw [List.map_map]
  change (Finset.univ.toList.map (fun k => outer (fun i => B i k))).sum = W
  rw [Finset.sum_map_toList]
  exact he

lemma positive_constrained_decomposition (W H : Matrix ι ι ℝ) (hW : W.PosSemidef)
    (hH : 0 ≤ pairing H W) :
    ∃ l : List (ι → ℝ), (l.map outer).sum = W ∧ ∀ v ∈ l, 0 ≤ qform H v := by
  obtain ⟨l, hl⟩ := positive_outer_decomposition W hW
  have hs : 0 ≤ (l.map (qform H)).sum := by
    rw [← hl, pairing_sum] at hH
    simpa only [List.map_map, Function.comp_def, ← qform_eq_pairing] using hH
  obtain ⟨k,hk,hpos⟩ := constrained_list_decomposition H l hs
  exact ⟨k,hk.trans hl,hpos⟩

end RobustLFTProof


open Matrix BigOperators

namespace RobustLFTProof
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def functionalMatrix (f : (Matrix ι ι ℝ) →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j => (f (Matrix.single i j 1) + f (Matrix.single j i 1))/2

lemma functional_expansion (f : (Matrix ι ι ℝ) →L[ℝ] ℝ) (A : Matrix ι ι ℝ) :
    f A = ∑ i, ∑ j, A i j * f (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h, map_smul, smul_eq_mul]

omit [Fintype ι] in
lemma functionalMatrix_symmetric (f : (Matrix ι ι ℝ) →L[ℝ] ℝ) :
    (functionalMatrix f).IsHermitian := by
  ext i j
  simp [functionalMatrix, add_comm]

omit [DecidableEq ι] in
private lemma symmetric_sum (a b : ι → ι → ℝ) (ha : ∀ i j, a j i = a i j) :
    (∑ i, ∑ j, a i j * ((b i j+b j i)/2)) = ∑ i, ∑ j, a i j*b i j := by
  simp only [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
  have he : (∑ i, ∑ j, a i j * b j i) = ∑ i, ∑ j, a i j * b i j := by
    rw [Finset.sum_comm]
    simp only [ha]
  rw [he]
  ring

lemma functionalMatrix_pairing (f : (Matrix ι ι ℝ) →L[ℝ] ℝ)
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : pairing A (functionalMatrix f) = f A := by
  have hs : ∀ i j, A j i = A i j := by
    intro i j
    simpa using congrFun (congrFun hA i) j
  rw [functional_expansion f A]
  exact symmetric_sum (fun i j => A i j) (fun i j => f (single i j 1)) hs

omit [Fintype ι] [DecidableEq ι] in
lemma outer_isHermitian (v : ι → ℝ) : (outer v).IsHermitian := by
  ext i j
  simp [outer, mul_comm]

lemma functionalMatrix_qform (f : (Matrix ι ι ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    qform (functionalMatrix f) v = f (outer v) := by
  rw [qform_eq_pairing]
  have hc : pairing (functionalMatrix f) (outer v) = pairing (outer v) (functionalMatrix f) := by
    simp only [pairing, mul_comm]
  rw [hc, functionalMatrix_pairing f _ (outer_isHermitian v)]

end RobustLFTProof


open Matrix Set Filter Topology

namespace RobustLFTProof
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma qform_outer_nonneg (v z : ι → ℝ) : 0 ≤ qform (outer v) z := by
  have he : qform (outer v) z = (z ⬝ᵥ v)^2 := by
    simp only [qform, outer, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, pow_two]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact sq_nonneg _

lemma functionalMatrix_posSemidef (f : (Matrix ι ι ℝ) →L[ℝ] ℝ)
    (hf : ∀ A ∈ positiveCone, 0 ≤ f A) : (functionalMatrix f).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨functionalMatrix_symmetric f, ?_⟩
  intro v
  change 0 ≤ qform (functionalMatrix f) v
  rw [functionalMatrix_qform]
  have hc : Continuous (fun t : ℝ => f (outer v + t • (1 : Matrix ι ι ℝ))) := by fun_prop
  have ht : Tendsto (fun t : ℝ => f (outer v + t • (1 : Matrix ι ι ℝ))) (𝓝[>] 0)
      (𝓝 (f (outer v))) := by
    have ht0 : Tendsto (fun t : ℝ => f (outer v + t • (1 : Matrix ι ι ℝ))) (𝓝[>] 0)
        (𝓝 (f (outer v + (0 : ℝ) • (1 : Matrix ι ι ℝ)))) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [zero_smul,add_zero] using ht0
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply hf
  intro z hz
  rw [qform_add_matrix,qform_smul_matrix]
  exact add_pos_of_nonneg_of_pos (qform_outer_nonneg v z)
    (mul_pos ht (one_mem_positiveCone z hz))

lemma separating_functional (F H : Matrix ι ι ℝ)
    (hn : ∀ s : ℝ, 0 ≤ s → F - s • H ∉ positiveCone) :
    ∃ f : (Matrix ι ι ℝ) →L[ℝ] ℝ,
      (∀ A ∈ positiveCone, 0 ≤ f A) ∧ f F ≤ 0 ∧ 0 ≤ f H ∧
      ∃ c : ℝ, f F ≤ c ∧ c < f 1 := by
  let R : Set (Matrix ι ι ℝ) := {A | ∃ s : ℝ, 0 ≤ s ∧ A = F-s • H}
  have hr : Convex ℝ R := by
    rintro A ⟨s,hs,rfl⟩ B ⟨t,ht,rfl⟩ a b ha hb hab
    refine ⟨a*s+b*t,add_nonneg (mul_nonneg ha hs) (mul_nonneg hb ht), ?_⟩
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    nlinarith [congrArg (fun c : ℝ => c * F i j) hab]
  have hd : Disjoint (positiveCone (ι := ι)) R := by
    rw [Set.disjoint_left]
    rintro A hA ⟨s,hs,rfl⟩
    exact hn s hs hA
  obtain ⟨g,u,hg,hrg⟩ := geometric_hahn_banach_open positiveCone_convex positiveCone_isOpen hr hd
  let f : (Matrix ι ι ℝ) →L[ℝ] ℝ := -g
  let c : ℝ := -u
  have hcone : ∀ A ∈ positiveCone, c < f A := by intro A hA; exact neg_lt_neg (hg A hA)
  have hray : ∀ s : ℝ, 0 ≤ s → f F-s*f H ≤ c := by
    intro s hs
    have hh := neg_le_neg (hrg (F-s • H) ⟨s,hs,rfl⟩)
    simpa [f,c,map_sub,map_smul,add_comm] using hh
  have hc : c ≤ 0 := by
    have ht : Tendsto (fun t : ℝ => t * f 1) (𝓝[>] 0) (𝓝 0) := by
      have hc0 : Continuous (fun t : ℝ => t * f 1) := by fun_prop
      have ht0 : Tendsto (fun t : ℝ => t * f 1) (𝓝[>] 0) (𝓝 (0 * f 1)) :=
        hc0.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [zero_mul] using ht0
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [map_smul,smul_eq_mul] using (hcone _ (positiveCone_smul one_mem_positiveCone ht)).le
  have hpos : ∀ A ∈ positiveCone, 0 ≤ f A := by
    intro A hA
    by_contra! hnA
    let t := (c-1)/f A
    have ht : 0 < t := div_pos_of_neg_of_neg (by linarith) hnA
    have hh := hcone _ (positiveCone_smul hA ht)
    have he : t*f A = c-1 := div_mul_cancel₀ _ hnA.ne
    simp only [map_smul,smul_eq_mul] at hh
    linarith
  have hF : f F ≤ c := by simpa using hray 0 le_rfl
  have hH : 0 ≤ f H := by
    by_contra! hnH
    let s := (f F-c-1)/f H
    have hs : 0 < s := div_pos_of_neg_of_neg (by linarith) hnH
    have he : s*f H = f F-c-1 := div_mul_cancel₀ _ hnH.ne
    have hh := hray s hs.le
    linarith
  exact ⟨f,hpos,hF.trans hc,hH,c,hF,hcone 1 one_mem_positiveCone⟩

lemma separating_psd_witness (F H : Matrix ι ι ℝ) (hF : F.IsHermitian) (hH : H.IsHermitian)
    (hn : ∀ s : ℝ, 0 ≤ s → F - s • H ∉ positiveCone) :
    ∃ W : Matrix ι ι ℝ, W.PosSemidef ∧ W ≠ 0 ∧ pairing F W ≤ 0 ∧ 0 ≤ pairing H W := by
  obtain ⟨f,hpos,hfF,hfH,c,hFc,hc⟩ := separating_functional F H hn
  refine ⟨functionalMatrix f,functionalMatrix_posSemidef f hpos,?_,?_,?_⟩
  · intro hz
    have h1 := functionalMatrix_pairing f 1 (Matrix.isHermitian_one)
    have h2 := functionalMatrix_pairing f F hF
    simp only [hz,pairing,Matrix.zero_apply,mul_zero,Finset.sum_const_zero] at h1 h2
    linarith
  · simpa only [functionalMatrix_pairing f F hF] using hfF
  · simpa only [functionalMatrix_pairing f H hH] using hfH

end RobustLFTProof


open Matrix Set Filter Topology

namespace RobustLFTProof
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma positive_pairing_of_decomposition (F W : Matrix ι ι ℝ) (l : List (ι → ℝ))
    (hl : (l.map outer).sum = W) (hW : W ≠ 0)
    (hpos : ∀ v ∈ l, v ≠ 0 → 0 < qform F v) : 0 < pairing F W := by
  have hn : ∀ v ∈ l, 0 ≤ qform F v := by
    intro v hv
    by_cases hz : v = 0
    · simp [hz,qform_zero]
    · exact (hpos v hv hz).le
  have hex : ∃ v ∈ l, v ≠ 0 := by
    by_contra! hh
    have hz : (l.map outer).sum = 0 := by
      apply List.sum_eq_zero
      intro A hA
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hA
      rw [hh v hv]
      ext i j
      simp [outer]
    exact hW (hl.symm.trans hz)
  obtain ⟨v,hv,hv0⟩ := hex
  have hle : qform F v ≤ (l.map (qform F)).sum := by
    exact List.single_le_sum (fun a ha => by
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
      exact hn z hz) (qform F v) (List.mem_map.mpr ⟨v,hv,rfl⟩)
  have hp := (hpos v hv hv0).trans_le hle
  rw [← hl,pairing_sum]
  simpa only [List.map_map,Function.comp_def,← qform_eq_pairing] using hp

lemma strict_slemma_nonnegative (F H : Matrix ι ι ℝ)
    (hF : F.IsHermitian) (hH : H.IsHermitian)
    (hp : ∀ v : ι → ℝ, v ≠ 0 → 0 ≤ qform H v → 0 < qform F v) :
    ∃ s : ℝ, 0 ≤ s ∧ F-s • H ∈ positiveCone := by
  by_contra! hn
  obtain ⟨W,hW,hW0,hFW,hHW⟩ := separating_psd_witness F H hF hH hn
  obtain ⟨l,hl,hpos⟩ := positive_constrained_decomposition W H hW hHW
  have hh := positive_pairing_of_decomposition F W l hl hW0
    (fun v hv hv0 => hp v hv0 (hpos v hv))
  exact (not_lt_of_ge hFW) hh

lemma strict_slemma (F H : Matrix ι ι ℝ)
    (hF : F.IsHermitian) (hH : H.IsHermitian)
    (hp : ∀ v : ι → ℝ, v ≠ 0 → 0 ≤ v ⬝ᵥ H *ᵥ v → 0 < v ⬝ᵥ F *ᵥ v) :
    ∃ s : ℝ, 0 < s ∧ (F-s • H).PosDef := by
  obtain ⟨s,hs,hpcone⟩ := strict_slemma_nonnegative F H hF hH hp
  have herm (t : ℝ) : (F-t • H).IsHermitian := hF.sub (hH.smul (by simp [IsSelfAdjoint]))
  rcases lt_or_eq_of_le hs with hs | hs
  · exact ⟨s,hs,(posDef_iff_positiveCone (herm s)).mpr hpcone⟩
  · subst s
    have hc : Continuous (fun t : ℝ => F-t • H) := by fun_prop
    have he : ∀ᶠ t : ℝ in 𝓝 0, F-t • H ∈ positiveCone :=
      hc.continuousAt.preimage_mem_nhds (positiveCone_isOpen.mem_nhds hpcone)
    have he' := he.filter_mono (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    obtain ⟨t,hcone,ht⟩ := (he'.and ht).exists
    exact ⟨t,ht,(posDef_iff_positiveCone (herm t)).mpr hcone⟩

end RobustLFTProof


noncomputable section
open Matrix
open RobustLS.LinFrac
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace RobustLFTProof
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem eucNorm_eq_norm (v : ι → ℝ) :
    eucNorm v = ‖WithLp.toLp 2 v‖ := by
  simp [eucNorm, EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]

theorem eucNorm_nonneg (v : ι → ℝ) : 0 ≤ eucNorm v := Real.sqrt_nonneg _

theorem eucNorm_sq (v : ι → ℝ) : eucNorm v ^ 2 = v ⬝ᵥ v := by
  unfold eucNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
  simp only [dotProduct, pow_two]

theorem eucNorm_eq_zero_iff (v : ι → ℝ) : eucNorm v = 0 ↔ v = 0 := by
  rw [eucNorm_eq_norm, norm_eq_zero]
  exact WithLp.toLp_eq_zero 2

theorem abs_dot_le (u v : ι → ℝ) : |u ⬝ᵥ v| ≤ eucNorm u * eucNorm v := by
  simpa [eucNorm_eq_norm, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    using abs_real_inner_le_norm (WithLp.toLp 2 u) (WithLp.toLp 2 v)

theorem specNorm_eq_norm [DecidableEq κ] (A : Matrix ι κ ℝ) : specNorm A = ‖A‖ := rfl

theorem specNorm_transpose [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    specNorm A.transpose = specNorm A := by
  have h : A.conjTranspose = A.transpose := by
    ext i j
    simp
  rw [specNorm_eq_norm, specNorm_eq_norm, ← h]
  exact Matrix.l2_opNorm_conjTranspose A

theorem eucNorm_mulVec_le [DecidableEq κ] (A : Matrix ι κ ℝ) (v : κ → ℝ) :
    eucNorm (A *ᵥ v) ≤ specNorm A * eucNorm v := by
  simpa only [eucNorm_eq_norm, specNorm, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLpLin_apply] using
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).le_opNorm
      (WithLp.toLp 2 v)

theorem contraction_mulVec [DecidableEq κ] (A : Matrix ι κ ℝ)
    (hA : specNorm A ≤ 1) (v : κ → ℝ) : eucNorm (A *ᵥ v) ≤ eucNorm v := by
  exact (eucNorm_mulVec_le A v).trans (by nlinarith [eucNorm_nonneg v])

theorem specNorm_le_one [DecidableEq κ] (A : Matrix ι κ ℝ)
    (h : ∀ v, eucNorm (A *ᵥ v) ≤ eucNorm v) : specNorm A ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul, eucNorm_eq_norm, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLpLin_apply, WithLp.toLp_ofLp] using h (WithLp.ofLp v)

end RobustLFTProof


noncomputable section
open Matrix
open RobustLS.LinFrac
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace RobustLFTProof
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sqrt_quadratic (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (v : ι → ℝ) :
    eucNorm (CFC.sqrt S *ᵥ v)^2 = v ⬝ᵥ S *ᵥ v := by
  rw [eucNorm_sq]
  have hs : (CFC.sqrt S).transpose = CFC.sqrt S := by
    ext i j
    simpa using congrFun (congrFun (CFC.sqrt_nonneg S).posSemidef.isHermitian i) j
  calc
    _ = (v ᵥ* (CFC.sqrt S).transpose) ⬝ᵥ CFC.sqrt S *ᵥ v := by
      rw [Matrix.vecMul_transpose]
    _ = v ⬝ᵥ ((CFC.sqrt S).transpose * CFC.sqrt S) *ᵥ v := by
      simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    _ = _ := by rw [hs, CFC.sqrt_mul_sqrt_self S hS.nonneg]

theorem weighted_contraction (S A : Matrix ι ι ℝ) (hS : S.PosSemidef)
    (hcomm : S * A = A * S) (hA : specNorm A ≤ 1) (v : ι → ℝ) :
    (A *ᵥ v) ⬝ᵥ S *ᵥ (A *ᵥ v) ≤ v ⬝ᵥ S *ᵥ v := by
  have hc : CFC.sqrt S * A = A * CFC.sqrt S := by
    have h : Commute S A := hcomm
    simpa only [← CFC.sqrt_eq_cfc] using (h.cfc_nnreal NNReal.sqrt).eq
  rw [← sqrt_quadratic S hS, ← sqrt_quadratic S hS]
  have he : CFC.sqrt S *ᵥ (A *ᵥ v) = A *ᵥ (CFC.sqrt S *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hc, Matrix.mulVec_mulVec]
  rw [he]
  exact pow_le_pow_left₀ (eucNorm_nonneg _) (contraction_mulVec A hA _) 2

theorem weighted_transpose_contraction (S A : Matrix ι ι ℝ) (hS : S.PosSemidef)
    (hcomm : S * A = A * S) (hA : specNorm A ≤ 1) (v : ι → ℝ) :
    (A.transpose *ᵥ v) ⬝ᵥ S *ᵥ (A.transpose *ᵥ v) ≤ v ⬝ᵥ S *ᵥ v := by
  apply weighted_contraction S A.transpose hS
  · have hs : S.transpose = S := by
      ext i j
      simpa using congrFun (congrFun hS.1 i) j
    simpa only [Matrix.transpose_mul, hs] using congrArg Matrix.transpose hcomm.symm
  · simpa only [specNorm_transpose] using hA

end RobustLFTProof


noncomputable section
open Matrix
open RobustLS.LinFrac
namespace RobustLFTProof
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem eucNorm_smul (c : ℝ) (v : ι → ℝ) : eucNorm (c • v) = |c| * eucNorm v := by
  simp only [eucNorm_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

theorem exists_contraction_mulVec (p q : ι → ℝ) (h : eucNorm p ≤ eucNorm q) :
    ∃ A : Matrix ι ι ℝ, specNorm A ≤ 1 ∧ A *ᵥ q = p := by
  by_cases hq : q = 0
  · have hp : p = 0 := (eucNorm_eq_zero_iff p).mp (by
      apply le_antisymm _ (eucNorm_nonneg p)
      simpa [hq, eucNorm] using h)
    subst p
    refine ⟨0, ?_, by simp⟩
    simp [specNorm, Matrix.toEuclideanLin]
  have hnq : 0 < eucNorm q := lt_of_le_of_ne (eucNorm_nonneg q) (Ne.symm ((eucNorm_eq_zero_iff q).not.mpr hq))
  have hqq : 0 < q ⬝ᵥ q := by rw [← eucNorm_sq]; positivity
  let A : Matrix ι ι ℝ := fun i j => p i * q j / (q ⬝ᵥ q)
  have hAv (v : ι → ℝ) : A *ᵥ v = ((q ⬝ᵥ v) / (q ⬝ᵥ q)) • p := by
    ext i
    simp only [A, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    simp only [div_mul_eq_mul_div, ← Finset.sum_div, mul_assoc, ← Finset.mul_sum]
    ring
  refine ⟨A, specNorm_le_one A (fun v => ?_), ?_⟩
  · rw [hAv, eucNorm_smul, abs_div, abs_of_pos hqq]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hqq).mpr
    have hv := abs_dot_le q v
    have hp := mul_le_mul_of_nonneg_left h (abs_nonneg (q ⬝ᵥ v))
    have hqv := mul_le_mul_of_nonneg_right hv (eucNorm_nonneg q)
    rw [← eucNorm_sq q]
    nlinarith
  · rw [hAv, div_self (ne_of_gt hqq), one_smul]

theorem exists_contraction_transpose_mulVec (p q : ι → ℝ)
    (h : eucNorm p ≤ eucNorm q) :
    ∃ A : Matrix ι ι ℝ, specNorm A ≤ 1 ∧ A.transpose *ᵥ q = p := by
  obtain ⟨A, hA, he⟩ := exists_contraction_mulVec p q h
  exact ⟨A.transpose, by simpa only [specNorm_transpose] using hA, by simpa using he⟩

end RobustLFTProof


noncomputable section
open Matrix
namespace RobustLFTProof
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def certificate (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D S G : Matrix κ κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks (T-B*S*B.transpose) (C.transpose-B*S*D.transpose+B*G)
    (C-D*S*B.transpose-G*B.transpose) (S-G*D.transpose+D*G-D*S*D.transpose)

def lft (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D A : Matrix κ κ ℝ) [DecidableEq κ] : Matrix ι ι ℝ :=
  T+B*A*(1-D*A)⁻¹*C+C.transpose*((1-D*A)⁻¹).transpose*A.transpose*B.transpose

theorem dot_move (A : Matrix ι κ ℝ) (u : ι → ℝ) (v : κ → ℝ) :
    u ⬝ᵥ A *ᵥ v = (A.transpose *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem skew_dot (G : Matrix κ κ ℝ) (hG : G.transpose = -G) (u v : κ → ℝ) :
    u ⬝ᵥ G *ᵥ v = -(v ⬝ᵥ G *ᵥ u) := by
  have h := Matrix.dotProduct_transpose_mulVec G v u
  rw [hG, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

theorem block_qform (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (u : ι → ℝ) (p : κ → ℝ) :
    qform (Matrix.fromBlocks A B C D) (Sum.elim u p) =
      u ⬝ᵥ A *ᵥ u + u ⬝ᵥ B *ᵥ p + p ⬝ᵥ C *ᵥ u + p ⬝ᵥ D *ᵥ p := by
  simp only [qform, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, dotProduct_add]
  ring

theorem certificate_qform (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D S G : Matrix κ κ ℝ) (hG : G.transpose = -G)
    (u : ι → ℝ) (p : κ → ℝ) :
    qform (certificate T B C D S G) (Sum.elim u p) =
      u ⬝ᵥ T *ᵥ u + 2 * (u ⬝ᵥ C.transpose *ᵥ p) + p ⬝ᵥ S *ᵥ p -
      (B.transpose *ᵥ u + D.transpose *ᵥ p) ⬝ᵥ
        S *ᵥ (B.transpose *ᵥ u + D.transpose *ᵥ p) +
      2 * ((B.transpose *ᵥ u + D.transpose *ᵥ p) ⬝ᵥ G *ᵥ p) := by
  rw [certificate, block_qform]
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_sub, dotProduct_add, Matrix.mulVec_add, add_dotProduct]
  simp only [dot_move B, dot_move D]
  rw [← Matrix.dotProduct_transpose_mulVec C u p,
    skew_dot G hG p (B.transpose *ᵥ u), skew_dot G hG p (D.transpose *ᵥ p)]
  ring

end RobustLFTProof


noncomputable section
open Matrix
namespace RobustLFTProof
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem det_ne_zero_of_kernel (M : Matrix κ κ ℝ)
    (h : ∀ v, M *ᵥ v = 0 → v = 0) : M.det ≠ 0 := by
  have hi : Function.Injective M.mulVec := by
    intro u v he
    apply sub_eq_zero.mp
    apply h
    rw [Matrix.mulVec_sub, he, sub_self]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi))

def feedback (B : Matrix ι κ ℝ) (D A : Matrix κ κ ℝ) (u : ι → ℝ) : κ → ℝ :=
  ((1-D*A)⁻¹).transpose *ᵥ (A.transpose *ᵥ (B.transpose *ᵥ u))

theorem feedback_equation (B : Matrix ι κ ℝ) (D A : Matrix κ κ ℝ)
    (h : (1-D*A).det ≠ 0) (u : ι → ℝ) :
    feedback B D A u = A.transpose *ᵥ (B.transpose *ᵥ u+D.transpose *ᵥ feedback B D A u) := by
  have hi : (1-A.transpose*D.transpose)*((1-D*A)⁻¹).transpose = 1 := by
    have hh := congrArg Matrix.transpose (Matrix.nonsing_inv_mul (1-D*A) (isUnit_iff_ne_zero.mpr h))
    simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one] using hh
  have he : (1-A.transpose*D.transpose) *ᵥ feedback B D A u = A.transpose *ᵥ B.transpose *ᵥ u := by
    unfold feedback
    rw [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at he
  rw [Matrix.mulVec_add]
  exact sub_eq_iff_eq_add.mp he

theorem feedback_unique (B : Matrix ι κ ℝ) (D A : Matrix κ κ ℝ)
    (h : (1-D*A).det ≠ 0) (u : ι → ℝ) (p : κ → ℝ)
    (hp : p = A.transpose *ᵥ (B.transpose *ᵥ u+D.transpose *ᵥ p)) :
    p = feedback B D A u := by
  have ht : (1-A.transpose*D.transpose).det ≠ 0 := by
    have he : 1-A.transpose*D.transpose = (1-D*A).transpose := by simp
    rw [he, Matrix.det_transpose]
    exact h
  apply Matrix.mulVec_injective_of_det_ne_zero ht
  have he := feedback_equation B D A h u
  simp only [Matrix.mulVec_add] at hp he
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  exact (sub_eq_iff_eq_add.mpr hp).trans (sub_eq_iff_eq_add.mpr he).symm

theorem lft_qform (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D A : Matrix κ κ ℝ) (u : ι → ℝ) :
    qform (lft T B C D A) u =
      u ⬝ᵥ T *ᵥ u + 2*(u ⬝ᵥ C.transpose *ᵥ feedback B D A u) := by
  simp only [qform, lft, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec]
  rw [dot_move B, dot_move A, dot_move ((1-D*A)⁻¹)]
  change u ⬝ᵥ T *ᵥ u + feedback B D A u ⬝ᵥ C *ᵥ u +
    u ⬝ᵥ C.transpose *ᵥ feedback B D A u = _
  rw [← Matrix.dotProduct_transpose_mulVec C u (feedback B D A u)]
  ring

end RobustLFTProof


noncomputable section
open Matrix
open RobustLS.LinFrac
namespace RobustLFTProof
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem skew_mixed_zero (G A : Matrix κ κ ℝ) (hG : G.transpose = -G)
    (hcomm : G*A=A*G) (hGA : (G*A).transpose = -(G*A))
    (p q : κ → ℝ) (hp : p=A.transpose *ᵥ q) : q ⬝ᵥ G *ᵥ p = 0 := by
  have he : p ⬝ᵥ G *ᵥ q = q ⬝ᵥ (G*A) *ᵥ q := by
    rw [hp, ← dot_move A, Matrix.mulVec_mulVec, ← hcomm]
  have hz := skew_dot (G*A) hGA q q
  have hg := skew_dot G hG q p
  linarith

theorem certificate_le (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D S G A : Matrix κ κ ℝ)
    (hS : S.PosSemidef) (hSA : S*A=A*S) (hA : specNorm A ≤ 1)
    (hG : G.transpose = -G) (hGAcomm : G*A=A*G)
    (hGA : (G*A).transpose = -(G*A)) (u : ι → ℝ) (p : κ → ℝ)
    (hp : p=A.transpose *ᵥ (B.transpose *ᵥ u+D.transpose *ᵥ p)) :
    qform (certificate T B C D S G) (Sum.elim u p) ≤
      u ⬝ᵥ T *ᵥ u + 2*(u ⬝ᵥ C.transpose *ᵥ p) := by
  rw [certificate_qform T B C D S G hG]
  have hw := weighted_transpose_contraction S A hS hSA hA
    (B.transpose *ᵥ u+D.transpose *ᵥ p)
  rw [← hp] at hw
  have hz := skew_mixed_zero G A hG hGAcomm hGA p
    (B.transpose *ᵥ u+D.transpose *ᵥ p) hp
  rw [hz]
  linarith

theorem certificate_nonsingular (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D S G A : Matrix κ κ ℝ)
    (hS : S.PosSemidef) (hSA : S*A=A*S) (hA : specNorm A ≤ 1)
    (hG : G.transpose = -G) (hGAcomm : G*A=A*G)
    (hGA : (G*A).transpose = -(G*A))
    (hcert : (certificate T B C D S G).PosDef) : (1-D*A).det ≠ 0 := by
  have ht : ((1-D*A).transpose).det ≠ 0 := by
    apply det_ne_zero_of_kernel
    intro p hp
    by_contra hpn
    have hpe : p=A.transpose *ᵥ (B.transpose *ᵥ (0 : ι → ℝ)+D.transpose *ᵥ p) := by
      simpa only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_zero, zero_add, sub_eq_zero] using hp
    have hn : Sum.elim (0 : ι → ℝ) p ≠ 0 := by
      intro he
      apply hpn
      ext i
      exact congrFun he (Sum.inr i)
    have hpos : 0 < qform (certificate T B C D S G) (Sum.elim (0 : ι → ℝ) p) := by
      simpa [qform] using hcert.dotProduct_mulVec_pos hn
    have hle := certificate_le T B C D S G A hS hSA hA hG hGAcomm hGA 0 p hpe
    simp only [zero_dotProduct] at hle
    linarith
  simpa only [Matrix.det_transpose] using ht

theorem certificate_lft_quadratic_pos (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D S G A : Matrix κ κ ℝ)
    (hS : S.PosSemidef) (hSA : S*A=A*S) (hA : specNorm A ≤ 1)
    (hG : G.transpose = -G) (hGAcomm : G*A=A*G)
    (hGA : (G*A).transpose = -(G*A))
    (hcert : (certificate T B C D S G).PosDef) (u : ι → ℝ) (hu : u ≠ 0) :
    0 < qform (lft T B C D A) u := by
  have hd := certificate_nonsingular T B C D S G A hS hSA hA hG hGAcomm hGA hcert
  let p := feedback B D A u
  have hn : Sum.elim u p ≠ 0 := by
    intro he
    apply hu
    ext i
    exact congrFun he (Sum.inl i)
  have hpos : 0 < qform (certificate T B C D S G) (Sum.elim u p) := by
    simpa [qform] using hcert.dotProduct_mulVec_pos hn
  have hle := certificate_le T B C D S G A hS hSA hA hG hGAcomm hGA u p
    (feedback_equation B D A hd u)
  rw [lft_qform]
  exact hpos.trans_le hle

end RobustLFTProof


noncomputable section
open Matrix
open RobustLS.LinFrac
namespace RobustLFTProof
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def border (lam : ℝ) (v : ι → ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks (lam • (1 : Matrix ι ι ℝ)) (Matrix.replicateCol Unit v)
    (Matrix.replicateRow Unit v) (lam • (1 : Matrix Unit Unit ℝ))

theorem border_qform (lam : ℝ) (v y : ι → ℝ) (t : ℝ) :
    qform (border lam v) (Sum.elim y (fun _ => t)) =
      lam*(y ⬝ᵥ y)+2*t*(v ⬝ᵥ y)+lam*t^2 := by
  have hc : Matrix.replicateCol Unit v *ᵥ (fun _ : Unit => t) = t • v := by
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hr : Matrix.replicateRow Unit v *ᵥ y = fun _ : Unit => v ⬝ᵥ y := by
    ext i
    rfl
  rw [border, block_qform, hc, hr]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  simp only [dotProduct, Fintype.sum_unique]
  have he : (∑ i, y i * v i) = ∑ i, v i * y i := by simp [mul_comm]
  rw [he]
  ring

omit [Fintype ι] in
theorem border_hermitian (lam : ℝ) (v : ι → ℝ) : (border lam v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  cases i <;> cases j <;> simp [border, Matrix.fromBlocks, Matrix.one_apply, eq_comm]

theorem border_posDef_iff (lam : ℝ) (v : ι → ℝ) :
    (border lam v).PosDef ↔ eucNorm v < lam := by
  constructor
  · intro h
    have hl : 0 < lam := by simpa [border] using h.diag_pos (i := Sum.inr ())
    by_contra! hs
    have hv : 0 < eucNorm v := hl.trans_le hs
    have hn : Sum.elim (-v) (fun _ : Unit => eucNorm v) ≠ 0 := by
      intro he
      have hz := congrFun he (Sum.inr ())
      exact hv.ne' hz
    have hp : 0 < qform (border lam v) (Sum.elim (-v) (fun _ => eucNorm v)) := by
      simpa [qform] using h.dotProduct_mulVec_pos hn
    rw [border_qform] at hp
    simp only [neg_dotProduct, dotProduct_neg, neg_neg] at hp
    rw [← eucNorm_sq v] at hp
    nlinarith [sq_nonneg (eucNorm v)]
  · intro hv
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (border_hermitian lam v) ?_
    intro z hz
    let y : ι → ℝ := fun i => z (Sum.inl i)
    let t : ℝ := z (Sum.inr ())
    have he : z = Sum.elim y (fun _ => t) := by
      ext (i | u)
      · rfl
      · cases u; rfl
    have hp : 0 < eucNorm y ^ 2 + t^2 := by
      by_contra! hh
      have hy : eucNorm y = 0 := by nlinarith [sq_nonneg (eucNorm y), sq_nonneg t]
      have ht : t = 0 := by nlinarith [sq_nonneg (eucNorm y), sq_nonneg t]
      apply hz
      rw [he, (eucNorm_eq_zero_iff y).mp hy, ht]
      ext (i | u) <;> rfl
    have hdot := abs_dot_le v y
    have hprod : |t*(v ⬝ᵥ y)| ≤ |t| *(eucNorm v*eucNorm y) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hdot (abs_nonneg t)
    have htwo : 2*|t| *eucNorm y ≤ eucNorm y^2+t^2 := by
      nlinarith [sq_nonneg (eucNorm y-|t|), sq_abs t]
    have hmul := mul_le_mul_of_nonneg_left htwo (eucNorm_nonneg v)
    have hlow := neg_abs_le (t*(v ⬝ᵥ y))
    have hstrict := mul_pos (sub_pos.mpr hv) hp
    change 0 < qform (border lam v) z
    rw [he, border_qform, ← eucNorm_sq]
    nlinarith

end RobustLFTProof


noncomputable section
open Matrix
open RobustLS.LinFrac
namespace RobustLFTProof
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def baseForm (T : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks T C.transpose C 0

def constraintForm (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks (B*B.transpose) (B*D.transpose) (D*B.transpose) (D*D.transpose-1)

omit [DecidableEq κ] in
theorem baseForm_qform (T : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) (u : ι → ℝ) (p : κ → ℝ) :
    qform (baseForm T C) (Sum.elim u p) = u ⬝ᵥ T *ᵥ u+2*(u ⬝ᵥ C.transpose *ᵥ p) := by
  rw [baseForm, block_qform]
  simp only [Matrix.zero_mulVec, dotProduct_zero]
  rw [← Matrix.dotProduct_transpose_mulVec C u p]
  ring

theorem constraintForm_qform (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) (u : ι → ℝ) (p : κ → ℝ) :
    qform (constraintForm B D) (Sum.elim u p) =
      eucNorm (B.transpose *ᵥ u+D.transpose *ᵥ p)^2-eucNorm p^2 := by
  rw [constraintForm, block_qform, eucNorm_sq, eucNorm_sq]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_sub, dotProduct_add, add_dotProduct, dot_move B, dot_move D]
  ring

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem baseForm_hermitian (T : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) (hT : T.IsHermitian) :
    (baseForm T C).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm] at hT ⊢
  unfold Matrix.IsSymm at hT ⊢
  simp only [baseForm, Matrix.fromBlocks_transpose, Matrix.transpose_transpose,
    Matrix.transpose_zero, hT]

omit [Fintype ι] in
theorem constraintForm_hermitian (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) :
    (constraintForm B D).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  unfold Matrix.IsSymm
  simp only [constraintForm, Matrix.fromBlocks_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_sub, Matrix.transpose_one]

omit [Fintype ι] in
theorem encoding_certificate (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (s : ℝ) :
    baseForm T C-s • constraintForm B D = certificate T B C D (s • 1) 0 := by
  ext (i | i) (j | j) <;>
    simp [baseForm, constraintForm, certificate, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
  ring

end RobustLFTProof


noncomputable section
open Matrix
open RobustLS.LinFrac
namespace RobustLFTProof
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem scalar_certificate (T : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (hT : T.IsHermitian)
    (hrob : ∀ A : Matrix κ κ ℝ, specNorm A ≤ 1 →
      (1-D*A).det ≠ 0 ∧ ∀ u : ι → ℝ, u ≠ 0 → 0 < qform (lft T B C D A) u) :
    ∃ s : ℝ, 0 < s ∧ (certificate T B C D (s • 1) 0).PosDef := by
  have hstrict : ∀ z : (ι ⊕ κ) → ℝ, z ≠ 0 →
      0 ≤ z ⬝ᵥ constraintForm B D *ᵥ z → 0 < z ⬝ᵥ baseForm T C *ᵥ z := by
    intro z hz hH
    let u : ι → ℝ := fun i => z (Sum.inl i)
    let p : κ → ℝ := fun i => z (Sum.inr i)
    have he : z=Sum.elim u p := by ext (i | i) <;> rfl
    change 0 ≤ qform (constraintForm B D) z at hH
    rw [he,constraintForm_qform] at hH
    have hn : eucNorm p ≤ eucNorm (B.transpose *ᵥ u+D.transpose *ᵥ p) := by
      nlinarith [eucNorm_nonneg p,eucNorm_nonneg (B.transpose *ᵥ u+D.transpose *ᵥ p)]
    obtain ⟨A,hA,hp⟩ := exists_contraction_transpose_mulVec p
      (B.transpose *ᵥ u+D.transpose *ᵥ p) hn
    obtain ⟨hd,hq⟩ := hrob A hA
    have hu : u ≠ 0 := by
      intro hu
      have hzero : (1-D*A).transpose *ᵥ p = 0 := by
        simp only [hu,Matrix.mulVec_zero,zero_add] at hp
        simp only [Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_mul,
          Matrix.sub_mulVec,Matrix.one_mulVec,← Matrix.mulVec_mulVec,hp,sub_self]
      have hp0 : p=0 := Matrix.eq_zero_of_mulVec_eq_zero
        (by simpa only [Matrix.det_transpose] using hd) hzero
      apply hz
      rw [he,hu,hp0]
      ext (i | i) <;> rfl
    have hpEq := feedback_unique B D A hd u p hp.symm
    have hval := hq u hu
    rw [lft_qform,← hpEq] at hval
    change 0 < qform (baseForm T C) z
    rwa [he,baseForm_qform]

  obtain ⟨s,hs,hpos⟩ := strict_slemma (baseForm T C) (constraintForm B D)
    (baseForm_hermitian T C hT) (constraintForm_hermitian B D) hstrict
  exact ⟨s,hs,by rwa [encoding_certificate] at hpos⟩

end RobustLFTProof


noncomputable section
open Matrix
open RobustLS.LinFrac
namespace RobustLFTProof
variable {n m N : ℕ}

def swapLast (ι κ : Type*) : ((ι ⊕ Unit) ⊕ κ) ≃ ((ι ⊕ κ) ⊕ Unit) where
  toFun := fun x => match x with
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr u) => Sum.inr u
    | Sum.inr j => Sum.inl (Sum.inr j)
  invFun := fun x => match x with
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr j) => Sum.inr j
    | Sum.inr u => Sum.inl (Sum.inr u)
  left_inv := by intro x; rcases x with (i | u) | j <;> rfl
  right_inv := by intro x; rcases x with (i | j) | u <;> rfl

def residualB (L : Matrix (Fin n) (Fin N) ℝ) : Matrix (Fin n ⊕ Unit) (Fin N) ℝ :=
  Matrix.fromRows L 0

def residualC (w : Fin N → ℝ) : Matrix (Fin N) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromCols 0 (Matrix.replicateCol Unit w)

theorem native_certificate_eq (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (L : Matrix (Fin n) (Fin N) ℝ) (RA : Matrix (Fin N) (Fin m) ℝ)
    (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ) (x : Fin m → ℝ)
    (lam : ℝ) (S G : Matrix (Fin N) (Fin N) ℝ) (hG : G.transpose = -G) :
    certificate (border lam (A *ᵥ x-b)) (residualB L) (residualC (RA *ᵥ x-Rb)) D S G =
      (lmiF A b L RA Rb D x lam S G).submatrix
        (swapLast (Fin n) (Fin N)) (swapLast (Fin n) (Fin N)) := by
  ext i j
  rcases i with (i | u) | k <;> rcases j with (j | v) | l <;>
    simp [certificate, border, residualB, residualC, lmiF, theta, swapLast,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      hG] <;> ring

theorem native_lft_eq (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (L : Matrix (Fin n) (Fin N) ℝ) (RA : Matrix (Fin N) (Fin m) ℝ)
    (Rb : Fin N → ℝ) (D Δ : Matrix (Fin N) (Fin N) ℝ) (x : Fin m → ℝ) (lam : ℝ) :
    lft (border lam (A *ᵥ x-b)) (residualB L) (residualC (RA *ᵥ x-Rb)) D Δ =
      border lam (pertA A L RA D Δ *ᵥ x-pertB b L Rb D Δ) := by
  let K := L * Δ * (1-D*Δ)⁻¹
  let w := RA *ᵥ x-Rb
  have hr : pertA A L RA D Δ *ᵥ x-pertB b L Rb D Δ =
      (A *ᵥ x-b)+K *ᵥ w := by
    simp only [pertA, pertB, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      K, w, Matrix.mulVec_sub]
    abel
  rw [hr]
  have ht : (residualC (n := n) w).transpose * ((1-D*Δ)⁻¹).transpose * Δ.transpose *
      (residualB L).transpose =
      (residualB L * Δ * (1-D*Δ)⁻¹ * residualC (n := n) w).transpose := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  change border lam (A *ᵥ x-b) + residualB L * Δ * (1-D*Δ)⁻¹ * residualC (n := n) w +
    (residualC (n := n) w).transpose * ((1-D*Δ)⁻¹).transpose * Δ.transpose *
      (residualB L).transpose = _
  rw [ht]
  have hc : residualB L * Δ * (1-D*Δ)⁻¹ * residualC (n := n) w =
      Matrix.fromBlocks 0 (Matrix.replicateCol Unit (K *ᵥ w)) 0 0 := by
    unfold residualB residualC
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    simp only [Matrix.zero_mul, Matrix.mul_zero]
    congr 1
  rw [hc]
  ext (i | u) (j | v) <;> simp [border, Matrix.transpose_apply]

end RobustLFTProof


open Matrix RobustLS.LinFrac

namespace RobustLFTProof

/-- El Ghaoui & Lebret (1997), Theorem 5.2, p. 1048 (PDF p. 14), **corrected**, with `ρ = 1`.
Printed: "When ρ = 1, an upper bound on the worst-case residual r_𝒟(A, b, x) can be obtained by
solving the SDP (40) inf_{S,G,λ} λ subject to S ∈ 𝒮, G ∈ 𝒢, (38). The upper bound is exact when
𝒟 = ℝ^{N×N}."
(a) Upper bound: every `λ` feasible for (40) — with the added constraints `S ≻ 0` and `GΔ`
skew-symmetric for every `Δ ∈ 𝒟` (see `residualBelow_of_certificate` for the counterexamples
to the printed version) — satisfies `λ > r_𝒟(A, b, x)`.
(b) Exactness for `𝒟 = ℝ^{N×N}`: every `λ > r_𝒟(A, b, x)` is feasible for (40), already with
`S = sI` (`s > 0`) and `G = 0`, which lie in `𝒮`, `𝒢` and satisfy the added constraints.
Together, the infimum (40) equals `r_𝒟(A, b, x)` when `𝒟 = ℝ^{N×N}`, including `r_𝒟 = ∞`
exactly when (40) is infeasible. The printed clause "If Θ > 0 at the optimum, the upper bound is
also exact" is not stated (the infimum over the strict LMI (38) is not attained). -/
theorem native_recovery {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    (∀ S G : Matrix (Fin N) (Fin N) ℝ, S ∈ symCommutant 𝒟 → G ∈ skewCommutant 𝒟 →
        (∀ Δ ∈ 𝒟, (G * Δ)ᵀ = -(G * Δ)) → S.PosDef →
        (lmiF A b L RA Rb D x lam S G).PosDef → ResidualBelow 𝒟 A b L RA Rb D x lam) ∧
    (𝒟 = ⊤ → ResidualBelow 𝒟 A b L RA Rb D x lam →
        ∃ s : ℝ, 0 < s ∧ (lmiF A b L RA Rb D x lam (s • 1) 0).PosDef) := by
  constructor
  · intro S G hSc hGc hGdelta hS hF
    have hG : G.transpose = -G := by
      have he := congrArg Matrix.transpose hGc.2
      simpa only [Matrix.transpose_neg, Matrix.transpose_transpose] using he
    have hcert := hF.submatrix (swapLast (Fin n) (Fin N)).injective
    rw [← native_certificate_eq A b L RA Rb D x lam S G hG] at hcert
    intro Δ hΔ hnorm
    have hcommS := hSc.1 Δ hΔ
    have hcommG := hGc.1 Δ hΔ
    have hd := certificate_nonsingular (border lam (A *ᵥ x-b)) (residualB L)
      (residualC (RA *ᵥ x-Rb)) D S G Δ hS.posSemidef hcommS hnorm hG hcommG
      (hGdelta Δ hΔ) hcert
    refine ⟨hd, (border_posDef_iff lam _).mp ?_⟩
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (border_hermitian lam _)
    intro u hu
    have hp := certificate_lft_quadratic_pos (border lam (A *ᵥ x-b)) (residualB L)
      (residualC (RA *ᵥ x-Rb)) D S G Δ hS.posSemidef hcommS hnorm hG hcommG
      (hGdelta Δ hΔ) hcert u hu
    rw [native_lft_eq] at hp
    simpa only [qform, star_trivial] using hp
  · intro hfull hrob
    have hscalar : ∀ Δ : Matrix (Fin N) (Fin N) ℝ, specNorm Δ ≤ 1 →
        (1-D*Δ).det ≠ 0 ∧ ∀ u : (Fin n ⊕ Unit) → ℝ, u ≠ 0 →
          0 < qform (lft (border lam (A *ᵥ x-b)) (residualB L)
            (residualC (RA *ᵥ x-Rb)) D Δ) u := by
      intro Δ hΔ
      obtain ⟨hd,hv⟩ := hrob Δ (by rw [hfull]; trivial) hΔ
      refine ⟨hd, fun u hu => ?_⟩
      rw [native_lft_eq]
      have hp := (border_posDef_iff lam _).mpr hv
      simpa only [qform, star_trivial] using hp.dotProduct_mulVec_pos hu
    obtain ⟨s,hs,hcert⟩ := scalar_certificate (border lam (A *ᵥ x-b))
      (residualB L) (residualC (RA *ᵥ x-Rb)) D (border_hermitian lam _) hscalar
    refine ⟨s,hs,?_⟩
    rw [native_certificate_eq A b L RA Rb D x lam (s • 1) 0 (by simp)] at hcert
    have hp := hcert.submatrix (swapLast (Fin n) (Fin N)).symm.injective
    simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] using hp

end RobustLFTProof


open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), Theorem 5.2, p. 1048 (PDF p. 14), **corrected**, with `ρ = 1`.
Printed: "When ρ = 1, an upper bound on the worst-case residual r_𝒟(A, b, x) can be obtained by
solving the SDP (40) inf_{S,G,λ} λ subject to S ∈ 𝒮, G ∈ 𝒢, (38). The upper bound is exact when
𝒟 = ℝ^{N×N}."
(a) Upper bound: every `λ` feasible for (40) — with the added constraints `S ≻ 0` and `GΔ`
skew-symmetric for every `Δ ∈ 𝒟` (see `residualBelow_of_certificate` for the counterexamples
to the printed version) — satisfies `λ > r_𝒟(A, b, x)`.
(b) Exactness for `𝒟 = ℝ^{N×N}`: every `λ > r_𝒟(A, b, x)` is feasible for (40), already with
`S = sI` (`s > 0`) and `G = 0`, which lie in `𝒮`, `𝒢` and satisfy the added constraints.
Together, the infimum (40) equals `r_𝒟(A, b, x)` when `𝒟 = ℝ^{N×N}`, including `r_𝒟 = ∞`
exactly when (40) is infeasible. The printed clause "If Θ > 0 at the optimum, the upper bound is
also exact" is not stated (the infimum over the strict LMI (38) is not attained). -/
theorem sdp_upper_bound_theorem52 {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    (∀ S G : Matrix (Fin N) (Fin N) ℝ, S ∈ symCommutant 𝒟 → G ∈ skewCommutant 𝒟 →
        (∀ Δ ∈ 𝒟, (G * Δ)ᵀ = -(G * Δ)) → S.PosDef →
        (lmiF A b L RA Rb D x lam S G).PosDef → ResidualBelow 𝒟 A b L RA Rb D x lam) ∧
    (𝒟 = ⊤ → ResidualBelow 𝒟 A b L RA Rb D x lam →
        ∃ s : ℝ, 0 < s ∧ (lmiF A b L RA Rb D x lam (s • 1) 0).PosDef) := by
  exact RobustLFTProof.native_recovery 𝒟 A b L RA Rb D x lam

end RobustLS.LinFrac

open RobustLS.LinFrac

theorem solution {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    (∀ S G : Matrix (Fin N) (Fin N) ℝ, S ∈ symCommutant 𝒟 → G ∈ skewCommutant 𝒟 →
        (∀ Δ ∈ 𝒟, (G * Δ)ᵀ = -(G * Δ)) → S.PosDef →
        (lmiF A b L RA Rb D x lam S G).PosDef → ResidualBelow 𝒟 A b L RA Rb D x lam) ∧
    (𝒟 = ⊤ → ResidualBelow 𝒟 A b L RA Rb D x lam →
        ∃ s : ℝ, 0 < s ∧ (lmiF A b L RA Rb D x lam (s • 1) 0).PosDef) := RobustLS.LinFrac.sdp_upper_bound_theorem52 𝒟 A b L RA Rb D x lam

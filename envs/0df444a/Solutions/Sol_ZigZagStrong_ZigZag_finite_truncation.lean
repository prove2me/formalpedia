-- Prove2me | solution 1 for ZigZagStrong.ZigZag.finite_truncation
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T21:07:20.828534+00:00
-- url     : https://prove2.me/submissions/4b38421b-8782-471c-98cd-90c3a93f4f49

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem tensorOp_apply' {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Matrix (Fin m) (Fin n) ℂ) (T : E →L[ℂ] E) (f : PiLp 2 (fun _ : Fin n => E)) (a : Fin m) :
    (StrongConv.tensorOp A T f) a = ∑ b, A a b • T (f b) := by
  classical
  simp [StrongConv.tensorOp, Finset.sum_apply, Pi.single_apply]

theorem rotation_apply' {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (bar : Equiv.Perm (Fin d)) (U : Fin d → E →L[ℂ] E)
    (f : Clouds d E) (i : Fin d) : (rotation bar U f) i = U (bar.symm i) (f (bar.symm i)) := rfl

theorem permL2_apply' {V : Type*} (e : Equiv.Perm V) (f : L2 V) (w : V) :
    (permL2 e f : V → ℂ) w = (f : V → ℂ) (e.symm w) := rfl

theorem gen_mul_self {d : ℕ} (t : Fin d) : involutionGenerator t * involutionGenerator t = 1 := by
  rw [involutionGenerator, ← map_mul]
  rw [show (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 from rfl, map_one]

theorem gen_inv {d : ℕ} (t : Fin d) : (involutionGenerator t)⁻¹ = involutionGenerator t :=
  inv_eq_of_mul_eq_one_right (gen_mul_self t)

theorem matchingLimit_apply {d c : ℕ} (H : Gadget d c) (f : TreeClouds d) (i : Fin d)
    (w : FreeInvolutions d) :
    (matchingLimit H f i : FreeInvolutions d → ℂ) w =
      ∑ t, ∑ b, (H.edges i t : ℂ) * H.edges t b * (f b : FreeInvolutions d → ℂ) (involutionGenerator t * w) := by
  rw [matchingLimit, zigzag, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    tensorOp_apply']
  simp only [rotation_apply', Equiv.refl_symm, Equiv.refl_apply, tensorOp_apply', regularL2,
    ContinuousLinearMap.id_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    map_sum, map_smul, permL2_apply', Equiv.coe_mulLeft, Equiv.mulLeft_symm, Gadget.mat, gen_inv]
  simp only [Finset.mul_sum, mul_assoc]



theorem topEdge_le_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (M : ℝ) :
    topEdge T ≤ M ↔ ∀ x : E, (inner ℂ (T x) x).re ≤ M * ‖x‖ ^ 2 := by
  have himg : Complex.re '' spectrum ℂ T = spectrum ℝ T := by
    rw [← hT.spectrumRestricts.algebraMap_image, Set.image_image]
    simp
  have hne : (spectrum ℝ T).Nonempty := by
    rw [← himg]; exact (spectrum.nonempty T).image _
  have hbdd : BddAbove (spectrum ℝ T) := by
    rw [← himg]; exact ((spectrum.isCompact T).image Complex.continuous_re).bddAbove
  unfold topEdge
  rw [himg, csSup_le_iff hbdd hne, ← le_algebraMap_iff_spectrum_le (A := E →L[ℂ] E) (R := ℝ) hT,
    ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  have hsa : IsSelfAdjoint (algebraMap ℝ (E →L[ℂ] E) M - T) :=
    (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all M)).sub hT
  simp only [hsa, true_and, ContinuousLinearMap.reApplyInnerSelf_apply]
  refine forall_congr' fun x => ?_
  have h1 : (algebraMap ℝ (E →L[ℂ] E) M - T) x = (M : ℂ) • x - T x := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h1, inner_sub_left, map_sub, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp only [RCLike.re_to_complex, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  have h2 : ((((‖x‖ : ℂ) ^ 2)).re) = ‖x‖ ^ 2 := by norm_cast
  have h3 : ((((‖x‖ : ℂ) ^ 2)).im) = 0 := by norm_cast
  simp only [zero_mul, sub_zero]
  erw [h2]
  constructor <;> intro h <;> linarith


theorem cloudCoord_apply {d : ℕ} (x : Fin d × FreeInvolutions d) (f : TreeClouds d) :
    cloudCoord x f = (f x.1 : FreeInvolutions d → ℂ) x.2 := rfl

theorem cloudCoord_delta {d : ℕ} (x y : Fin d × FreeInvolutions d) :
    cloudCoord x (cloudDelta y) = if x = y then 1 else 0 := by
  classical
  rw [cloudCoord_apply, cloudDelta]
  rcases x with ⟨i, w⟩; rcases y with ⟨j, v⟩
  by_cases hij : i = j
  · subst hij
    by_cases hwv : w = v
    · subst hwv; simp
    · simp [hwv, lp.single_apply]
  · simp [hij]

theorem matchingLimit_coord {d c : ℕ} (H : Gadget d c) (x y : Fin d × FreeInvolutions d) :
    cloudCoord x (matchingLimit H (cloudDelta y)) = (matchingKernel H x y : ℂ) := by
  classical
  rw [cloudCoord_apply, matchingLimit_apply]
  simp only [← cloudCoord_apply (d := d) (_, _), cloudCoord_delta, Prod.ext_iff]
  unfold matchingKernel
  push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single y.1]
  · by_cases h : involutionGenerator t * x.2 = y.2 <;> simp [h]
  · intro b _ hb; simp [hb]
  · simp

theorem inner_cloudDelta_left {d : ℕ} (x : Fin d × FreeInvolutions d) (f : TreeClouds d) :
    inner ℂ (cloudDelta x) f = cloudCoord x f := by
  classical
  rw [cloudDelta, PiLp.inner_apply, Finset.sum_eq_single x.1]
  · rw [PiLp.single_apply, if_pos rfl, lp.inner_single_left]
    simp [cloudCoord_apply]
  · intro b _ hb
    rw [PiLp.single_apply, if_neg hb, inner_zero_left]
  · simp

theorem ext_cloudCoord {d : ℕ} {f g : TreeClouds d} (h : ∀ x, cloudCoord x f = cloudCoord x g) :
    f = g := by
  ext i w
  exact h (i, w)

theorem dense_span_cloudDelta (d : ℕ) :
    Dense ((Submodule.span ℂ (Set.range (cloudDelta (d := d))) : Submodule ℂ (TreeClouds d)) :
      Set (TreeClouds d)) := by
  classical
  set K := (Submodule.span ℂ (Set.range (cloudDelta (d := d)))).topologicalClosure
  have hK : ∀ f : TreeClouds d, f ∈ K := by
    intro f
    have hf : f = ∑ i : Fin d, PiLp.single 2 i (f i) := by
      ext j w
      simp [PiLp.single_apply]
    rw [hf]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hs := lp.hasSum_single (E := fun _ : FreeInvolutions d => ℂ) (p := 2) (by norm_num) (f i)
    let L : L2 (FreeInvolutions d) →L[ℂ] TreeClouds d :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin d => L2 (FreeInvolutions d))).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℂ (fun _ : Fin d => L2 (FreeInvolutions d)) i)
    have hL : ∀ v, L v = PiLp.single 2 i v := fun v => rfl
    have hs2 := hs.mapL L
    rw [hL] at hs2
    refine (Submodule.span ℂ (Set.range (cloudDelta (d := d)))).isClosed_topologicalClosure.mem_of_tendsto hs2 (Eventually.of_forall fun s => ?_)
    refine Submodule.sum_mem _ fun w _ => Submodule.le_topologicalClosure _ ?_
    have : PiLp.single 2 i (lp.single 2 w ((f i : FreeInvolutions d → ℂ) w)) =
        ((f i : FreeInvolutions d → ℂ) w) • cloudDelta (i, w) := by
      ext j v
      by_cases hj : j = i
      · subst hj; by_cases hv : v = w
        · subst hv; simp [cloudDelta]
        · simp [cloudDelta, hv, Pi.single_apply]
      · simp [cloudDelta, hj, PiLp.single_apply]
    simp only [hL]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact Submodule.eq_top_iff'.mpr hK


theorem edges_symm {d c : ℕ} (H : Gadget d c) (i j : Fin d) : H.edges i j = H.edges j i :=
  congrArg (fun A : Matrix (Fin d) (Fin d) ℕ => A j i) H.symmetric.eq

theorem gen_mul_eq_iff {d : ℕ} (t : Fin d) (v w : FreeInvolutions d) :
    involutionGenerator t * v = w ↔ involutionGenerator t * w = v := by
  constructor <;> intro h <;> rw [← h, ← mul_assoc, gen_mul_self, one_mul]

theorem matchingKernel_symm {d c : ℕ} (H : Gadget d c) (x y : Fin d × FreeInvolutions d) :
    matchingKernel H x y = matchingKernel H y x := by
  classical
  unfold matchingKernel
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : involutionGenerator s * x.2 = y.2
  · have h' := (gen_mul_eq_iff s x.2 y.2).mp h
    simp only [h, h', if_true]
    rw [edges_symm H x.1 s, edges_symm H s y.1, Nat.mul_comm]
  · have h' : ¬ involutionGenerator s * y.2 = x.2 := fun h' => h ((gen_mul_eq_iff s y.2 x.2).mp h')
    simp only [h, h', if_false]

theorem truncatedKernel_symm {d c : ℕ} (H : Gadget d c) (a t : Fin d)
    (x y : Fin d × FreeInvolutions d) :
    truncatedKernel H a t x y = truncatedKernel H a t y x := by
  classical
  unfold truncatedKernel
  simp only
  by_cases hx : x = (a, 1) <;> by_cases hy : y = (a, 1)
  · subst hx; subst hy; rfl
  · simp [hx, hy]
  · simp [hx, hy]
  · simp only [hx, hy, if_false]
    rw [matchingKernel_symm H x y]
    congr 1
    exact propext ⟨fun h => h.symm, fun h => h.symm⟩

theorem truncatedKernel_le {d c : ℕ} (H : Gadget d c) (a t : Fin d) (hat : 0 < H.edges a t)
    (x y : Fin d × FreeInvolutions d) : truncatedKernel H a t x y ≤ matchingKernel H x y := by
  classical
  unfold truncatedKernel
  simp only
  by_cases hx : x = (a, 1)
  · subst hx
    simp only [if_true]
    split_ifs with hy
    · unfold matchingKernel
      refine le_trans ?_ (Finset.single_le_sum (f := fun s => if involutionGenerator s * (1 : FreeInvolutions d) = y.2
        then H.edges a s * H.edges s y.1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
      simp only [mul_one, hy, if_true]
      exact Nat.le_mul_of_pos_left _ hat
    · exact Nat.zero_le _
  · simp only [hx, if_false]
    by_cases hy : y = (a, 1)
    · subst hy
      simp only [if_true]
      split_ifs with hx2
      · unfold matchingKernel
        refine le_trans ?_ (Finset.single_le_sum (f := fun s => if involutionGenerator s * x.2 = 1
          then H.edges x.1 s * H.edges s a else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
        simp only [hx2, gen_mul_self, if_true]
        rw [edges_symm H x.1 t, edges_symm H t a]
        exact Nat.le_mul_of_pos_right _ hat
      · exact Nat.zero_le _
    · simp only [hy, if_false]
      split_ifs
      · exact Nat.zero_le _
      · exact le_rfl

theorem truncatedKernel_eq_of_ne_one {d c : ℕ} (H : Gadget d c) (a t : Fin d)
    (x y : Fin d × FreeInvolutions d) (hx : x.2 ≠ 1) (hy : y.2 ≠ 1) :
    truncatedKernel H a t x y = matchingKernel H x y := by
  classical
  unfold truncatedKernel
  have hx' : x ≠ (a, 1) := fun h => hx (by rw [h])
  have hy' : y ≠ (a, 1) := fun h => hy (by rw [h])
  simp [hx', hy', hx, hy]

theorem matchingKernel_ne_zero {d c : ℕ} (H : Gadget d c) (x y : Fin d × FreeInvolutions d)
    (h : matchingKernel H x y ≠ 0) : ∃ s, involutionGenerator s * x.2 = y.2 := by
  classical
  unfold matchingKernel at h
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases h' : involutionGenerator s * x.2 = y.2
  · exact ⟨s, h'⟩
  · simp [h'] at hs

theorem mem_changed_of_ne {d c : ℕ} (H : Gadget d c) (a t : Fin d)
    (x y : Fin d × FreeInvolutions d) (h : truncatedKernel H a t x y ≠ matchingKernel H x y) :
    x ∈ changedVertices d ∧ y ∈ changedVertices d := by
  classical
  have hC : ∀ z : Fin d × FreeInvolutions d, z ∈ changedVertices d ↔
      z.2 = 1 ∨ ∃ s, involutionGenerator s = z.2 := by
    intro z
    simp [changedVertices, Finset.mem_product, eq_comm]
  rw [hC, hC]
  by_contra hcon
  apply h
  by_cases hx1 : x.2 = 1 <;> by_cases hy1 : y.2 = 1
  · exact absurd ⟨Or.inl hx1, Or.inl hy1⟩ hcon
  · have hK : matchingKernel H x y = 0 := by
      by_contra hne
      obtain ⟨s, hs⟩ := matchingKernel_ne_zero H x y hne
      rw [hx1, mul_one] at hs
      exact hcon ⟨Or.inl hx1, Or.inr ⟨s, hs⟩⟩
    rw [hK]
    unfold truncatedKernel
    have hy' : y ≠ (a, 1) := fun h => hy1 (by rw [h])
    by_cases hx' : x = (a, 1)
    · simp only [hx', if_true]
      split_ifs with hu
      · exact absurd ⟨Or.inl hx1, Or.inr ⟨t, hu.symm⟩⟩ hcon
      · rfl
    · simp only [hx', hy', if_false]
      split_ifs with hu
      · rfl
      · exact hK
  · have hK : matchingKernel H x y = 0 := by
      by_contra hne
      rw [matchingKernel_symm] at hne
      obtain ⟨s, hs⟩ := matchingKernel_ne_zero H y x hne
      rw [hy1, mul_one] at hs
      exact hcon ⟨Or.inr ⟨s, hs⟩, Or.inl hy1⟩
    rw [hK]
    unfold truncatedKernel
    have hx' : x ≠ (a, 1) := fun h => hx1 (by rw [h])
    by_cases hy' : y = (a, 1)
    · simp only [hx', hy', if_true, if_false]
      split_ifs with hu
      · exact absurd ⟨Or.inr ⟨t, hu.symm⟩, Or.inl hy1⟩ hcon
      · rfl
    · simp only [hx', hy', if_false]
      split_ifs with hu
      · rfl
      · exact hK
  · exact truncatedKernel_eq_of_ne_one H a t x y hx1 hy1

theorem deletedAdj_coord {d c : ℕ} (H : Gadget d c) (a t : Fin d) (x y : Fin d × FreeInvolutions d) :
    cloudCoord x (deletedAdj H a t (cloudDelta y)) = (truncatedKernel H a t x y : ℂ) := by
  classical
  rw [deletedAdj, add_apply, map_add, matchingLimit_coord]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply, map_sum, map_smul, cloudCoord_delta,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
  by_cases h : truncatedKernel H a t x y = matchingKernel H x y
  · rw [h]
    split_ifs <;> simp [h]
  · obtain ⟨hx, hy⟩ := mem_changed_of_ne H a t x y h
    simp [hx, hy]

theorem isSelfAdjoint_of_coord {d : ℕ} (T : TreeClouds d →L[ℂ] TreeClouds d)
    (k : Fin d × FreeInvolutions d → Fin d × FreeInvolutions d → ℕ)
    (hk : ∀ x y, cloudCoord x (T (cloudDelta y)) = k x y) (hsym : ∀ x y, k x y = k y x) :
    IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine ContinuousLinearMap.ext_on (dense_span_cloudDelta d) ?_
  rintro _ ⟨y, rfl⟩
  refine ext_cloudCoord fun x => ?_
  rw [← inner_cloudDelta_left, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
    inner_cloudDelta_left, hk, hk, hsym]
  simp

theorem matchingLimit_selfAdjoint {d c : ℕ} (H : Gadget d c) :
    IsSelfAdjoint (matchingLimit H) :=
  isSelfAdjoint_of_coord _ _ (matchingLimit_coord H) (matchingKernel_symm H)

theorem deletedAdj_selfAdjoint {d c : ℕ} (H : Gadget d c) (a t : Fin d) :
    IsSelfAdjoint (deletedAdj H a t) :=
  isSelfAdjoint_of_coord _ _ (deletedAdj_coord H a t) (truncatedKernel_symm H a t)

theorem truncatedAdj_inner {d c : ℕ} (H : Gadget d c) (a t : Fin d) (u v : truncationSpace H a t) :
    inner ℂ (truncatedAdj H a t u) v = inner ℂ (deletedAdj H a t u) (v : TreeClouds d) := by
  rw [truncatedAdj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rfl

theorem truncatedAdj_selfAdjoint {d c : ℕ} (H : Gadget d c) (a t : Fin d) :
    IsSelfAdjoint (truncatedAdj H a t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  change inner ℂ (truncatedAdj H a t u) v = inner ℂ u (truncatedAdj H a t v)
  have hs := (deletedAdj_selfAdjoint H a t).isSymmetric (v : TreeClouds d) (u : TreeClouds d)
  simp only [ContinuousLinearMap.coe_coe] at hs
  rw [truncatedAdj_inner, ← inner_conj_symm u, truncatedAdj_inner, hs, inner_conj_symm]


abbrev Vtx (d : ℕ) := Fin d × FreeInvolutions d

theorem inner_sum_delta {d : ℕ} {ι : Type*} (T : TreeClouds d →L[ℂ] TreeClouds d)
    (S : Finset ι) (p : ι → Vtx d) (c : ι → ℂ) :
    inner ℂ (∑ i ∈ S, c i • cloudDelta (p i)) (T (∑ j ∈ S, c j • cloudDelta (p j))) =
      ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * cloudCoord (p i) (T (cloudDelta (p j))) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_cloudDelta_left, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_assoc]

theorem norm_sq_sum_delta {d : ℕ} {ι : Type*} (S : Finset ι) (p : ι → Vtx d) (c : ι → ℂ)
    (hp : Set.InjOn p S) :
    ‖∑ i ∈ S, c i • cloudDelta (p i)‖ ^ 2 = ∑ i ∈ S, ‖c i‖ ^ 2 := by
  classical
  have h := inner_sum_delta (ContinuousLinearMap.id ℂ (TreeClouds d)) S p c
  simp only [ContinuousLinearMap.id_apply, cloudCoord_delta] at h
  have h2 : ∀ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * (if p i = p j then (1 : ℂ) else 0) =
      (starRingEnd ℂ) (c i) * c i := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have : p i ≠ p j := fun h => hji (hp hj hi h.symm)
      simp [this]
    · intro h; exact absurd hi h
  rw [Finset.sum_congr rfl h2] at h
  rw [← @inner_self_eq_norm_sq ℂ, RCLike.re_to_complex, h, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem re_inner_sum_delta_le {d : ℕ} (T : TreeClouds d →L[ℂ] TreeClouds d)
    (k : Vtx d → Vtx d → ℕ) (hk : ∀ x y, cloudCoord x (T (cloudDelta y)) = k x y)
    (S : Finset (Vtx d)) (c : Vtx d → ℂ) :
    (inner ℂ (T (∑ x ∈ S, c x • cloudDelta x)) (∑ x ∈ S, c x • cloudDelta x)).re ≤
      ∑ x ∈ S, ∑ y ∈ S, ‖c x‖ * ‖c y‖ * (k x y : ℝ) := by
  have hq := inner_sum_delta T S id c
  simp only [id] at hq
  rw [← inner_conj_symm, Complex.conj_re, hq]
  simp only [hk, Complex.re_sum]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  refine (Complex.re_le_norm _).trans (le_of_eq ?_)
  simp [norm_mul]

theorem re_inner_sum_delta_eq {d : ℕ} {ι : Type*} (T : TreeClouds d →L[ℂ] TreeClouds d)
    (k : Vtx d → Vtx d → ℕ) (hk : ∀ x y, cloudCoord x (T (cloudDelta y)) = k x y)
    (S : Finset ι) (p : ι → Vtx d) (c : ι → ℝ) :
    (inner ℂ (T (∑ i ∈ S, (c i : ℂ) • cloudDelta (p i))) (∑ i ∈ S, (c i : ℂ) • cloudDelta (p i))).re =
      ∑ i ∈ S, ∑ j ∈ S, c i * c j * (k (p i) (p j) : ℝ) := by
  rw [← inner_conj_symm, Complex.conj_re, inner_sum_delta T S p (fun i => (c i : ℂ))]
  simp only [hk, Complex.re_sum, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  norm_cast

theorem nontrivial_treeClouds {d : ℕ} (hd : 0 < d) : Nontrivial (TreeClouds d) :=
  ⟨⟨cloudDelta (⟨0, hd⟩, 1), 0, fun h => by
    have := congrArg (cloudCoord (⟨0, hd⟩, 1)) h
    simp [cloudCoord_delta] at this⟩⟩

theorem mem_span_delta {d : ℕ} (f : TreeClouds d)
    (hf : f ∈ Submodule.span ℂ (Set.range (cloudDelta (d := d)))) :
    ∃ (S : Finset (Vtx d)) (c : Vtx d → ℂ), f = ∑ x ∈ S, c x • cloudDelta x := by
  obtain ⟨l, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
  exact ⟨l.support, l, rfl⟩

/-- A quadratic-form bound proved on finitely supported vectors extends to all vectors. -/
theorem rayleigh_bound_of_finite {d : ℕ} (T : TreeClouds d →L[ℂ] TreeClouds d) (M : ℝ)
    (h : ∀ (S : Finset (Vtx d)) (c : Vtx d → ℂ),
      (inner ℂ (T (∑ x ∈ S, c x • cloudDelta x)) (∑ x ∈ S, c x • cloudDelta x)).re ≤
        M * ‖∑ x ∈ S, c x • cloudDelta x‖ ^ 2) (f : TreeClouds d) :
    (inner ℂ (T f) f).re ≤ M * ‖f‖ ^ 2 := by
  have hcl : IsClosed {f : TreeClouds d | (inner ℂ (T f) f).re ≤ M * ‖f‖ ^ 2} :=
    isClosed_le (Complex.continuous_re.comp ((T.continuous).inner continuous_id))
      (continuous_const.mul (continuous_norm.pow 2))
  have hsub : (Submodule.span ℂ (Set.range (cloudDelta (d := d))) : Set (TreeClouds d)) ⊆
      {f : TreeClouds d | (inner ℂ (T f) f).re ≤ M * ‖f‖ ^ 2} := by
    intro g hg
    obtain ⟨S, c, rfl⟩ := mem_span_delta g hg
    exact h S c
  have := hcl.closure_subset_iff.mpr hsub
  rw [(dense_span_cloudDelta d).closure_eq] at this
  exact this (Set.mem_univ f)

theorem topEdge_truncated_le {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d)
    (a t : Fin d) (hat : 0 < H.edges a t) :
    topEdge (truncatedAdj H a t) ≤ topEdge (matchingLimit H) := by
  classical
  have := nontrivial_treeClouds (d := d) (by omega)
  set lamA := topEdge (matchingLimit H)
  have hA := (topEdge_le_iff (matchingLimit H) (matchingLimit_selfAdjoint H) lamA).mp le_rfl
  have hD : ∀ f : TreeClouds d, (inner ℂ (deletedAdj H a t f) f).re ≤ lamA * ‖f‖ ^ 2 := by
    refine rayleigh_bound_of_finite _ _ fun S c => ?_
    refine (re_inner_sum_delta_le _ _ (deletedAdj_coord H a t) S c).trans ?_
    have h1 := hA (∑ x ∈ S, (‖c x‖ : ℂ) • cloudDelta x)
    have e1 := re_inner_sum_delta_eq _ _ (matchingLimit_coord H) S id (fun x => ‖c x‖)
    have e2 := norm_sq_sum_delta S id (fun x => ((‖c x‖ : ℝ) : ℂ)) (Set.injOn_id _)
    have e3 := norm_sq_sum_delta S id c (Set.injOn_id _)
    simp only [id] at e1 e2 e3
    rw [e1, e2] at h1
    rw [e3]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm] at h1
    refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_) h1
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast truncatedKernel_le H a t hat x y)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have : Nontrivial (truncationSpace H a t) := by
    refine ⟨⟨⟨cloudDelta (a, 1), ?_⟩, 0, fun h => ?_⟩⟩
    · exact Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨(a, 1), Relation.ReflTransGen.refl, rfl⟩)
    · have := congrArg (fun w : truncationSpace H a t => cloudCoord (a, 1) (w : TreeClouds d)) h
      simp [cloudCoord_delta] at this
  rw [topEdge_le_iff _ (truncatedAdj_selfAdjoint H a t)]
  intro w
  rw [truncatedAdj_inner]
  exact hD w


theorem truncationSpace_nontrivial {d c : ℕ} (H : Gadget d c) (a t : Fin d) :
    Nontrivial (truncationSpace H a t) := by
  refine ⟨⟨⟨cloudDelta (a, 1), ?_⟩, 0, fun h => ?_⟩⟩
  · exact Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨(a, 1), Relation.ReflTransGen.refl, rfl⟩)
  · have := congrArg (fun w : truncationSpace H a t => cloudCoord (a, 1) (w : TreeClouds d)) h
    simp [cloudCoord_delta] at this

/-- Rayleigh bound for vectors supported on the root component, read through an injective
permGenling `Φ`. -/
theorem rayleigh_on_component {d c : ℕ} (H : Gadget d c) (a t : Fin d)
    (S : Finset (Vtx d)) (Φ : Vtx d → Vtx d) (hΦ : Set.InjOn Φ S)
    (hX : ∀ x ∈ S, Φ x ∈ truncationVertices H a t) (f : Vtx d → ℝ) :
    ∑ x ∈ S, ∑ y ∈ S, f x * f y * (truncatedKernel H a t (Φ x) (Φ y) : ℝ) ≤
      topEdge (truncatedAdj H a t) * ∑ x ∈ S, f x ^ 2 := by
  have := truncationSpace_nontrivial H a t
  have hμ := (topEdge_le_iff (truncatedAdj H a t) (truncatedAdj_selfAdjoint H a t)
    (topEdge (truncatedAdj H a t))).mp le_rfl
  set g : TreeClouds d := ∑ x ∈ S, (f x : ℂ) • cloudDelta (Φ x) with hg
  have hgW : g ∈ truncationSpace H a t := by
    refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ ?_
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨Φ x, hX x hx, rfl⟩)
  have h1 := hμ ⟨g, hgW⟩
  rw [truncatedAdj_inner] at h1
  have e1 := re_inner_sum_delta_eq _ _ (deletedAdj_coord H a t) S Φ f
  have e2 := norm_sq_sum_delta S Φ (fun x => (f x : ℂ)) hΦ
  rw [← hg] at e1 e2
  have e3 : ‖(⟨g, hgW⟩ : truncationSpace H a t)‖ = ‖g‖ := rfl
  rw [e3, e2, e1] at h1
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h1

/-- The homomorphism `ℤ/2 → G` sending the generator to an involution `g`. -/
def invHom {G : Type*} [Group G] (g : G) (hg : g * g = 1) : Multiplicative (ZMod 2) →* G where
  toFun z := if Multiplicative.toAdd z = 0 then 1 else g
  map_one' := by simp
  map_mul' := by
    intro x y
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases h2 (Multiplicative.toAdd x) with hx | hx <;>
      rcases h2 (Multiplicative.toAdd y) with hy | hy <;>
      simp [toAdd_mul, hx, hy, hg, h11]

theorem invHom_gen {G : Type*} [Group G] (g : G) (hg : g * g = 1) :
    invHom g hg (Multiplicative.ofAdd (1 : ZMod 2)) = g := by
  simp [invHom]

/-- Map to the infinite dihedral group: `g_t ↦ sr 0`, `g_s ↦ sr 1`, other generators to `1`. -/
def dihedralMap {d : ℕ} (t s : Fin d) : FreeInvolutions d →* DihedralGroup 0 :=
  Monoid.CoprodI.lift fun i =>
    if i = t then invHom (DihedralGroup.sr 0) (DihedralGroup.sr_mul_self 0)
    else if i = s then invHom (DihedralGroup.sr 1) (DihedralGroup.sr_mul_self 1)
    else 1

theorem dihedralMap_t {d : ℕ} (t s : Fin d) :
    dihedralMap t s (involutionGenerator t) = DihedralGroup.sr 0 := by
  simp [dihedralMap, involutionGenerator, Monoid.CoprodI.lift_of, invHom_gen]

theorem dihedralMap_s {d : ℕ} (t s : Fin d) (hst : s ≠ t) :
    dihedralMap t s (involutionGenerator s) = DihedralGroup.sr 1 := by
  simp [dihedralMap, involutionGenerator, Monoid.CoprodI.lift_of, invHom_gen, hst]

/-- The clouds `(g_t g_s)^n g_t` along which the root component escapes to infinity. -/
def escape {d : ℕ} (t s : Fin d) (n : ℕ) : FreeInvolutions d :=
  (involutionGenerator t * involutionGenerator s) ^ n * involutionGenerator t

theorem dihedralMap_escape {d : ℕ} (t s : Fin d) (hst : s ≠ t) (n : ℕ) :
    dihedralMap t s (escape t s n) = DihedralGroup.sr (-(n : ZMod 0)) := by
  rw [escape, map_mul, map_pow, map_mul, dihedralMap_t, dihedralMap_s t s hst,
    DihedralGroup.sr_mul_sr, show ((1 : ZMod 0) - 0) = 1 from by simp, DihedralGroup.r_one_pow,
    DihedralGroup.r_mul_sr]
  congr 1
  ring

theorem escape_injective {d : ℕ} (t s : Fin d) (hst : s ≠ t) :
    Function.Injective (escape t s) := by
  intro n m h
  have := congrArg (dihedralMap t s) h
  rw [dihedralMap_escape t s hst, dihedralMap_escape t s hst] at this
  have h2 := DihedralGroup.sr.inj this
  have h3 : (-(n : ℤ)) = -(m : ℤ) := h2
  omega

theorem escape_ne_one {d : ℕ} (t s : Fin d) (hst : s ≠ t) (n : ℕ) : escape t s n ≠ 1 := by
  intro h
  have := congrArg (dihedralMap t s) h
  rw [dihedralMap_escape t s hst, map_one, DihedralGroup.one_def] at this
  cases this

theorem gen_mul_escape_ne_one {d : ℕ} (t s : Fin d) (hst : s ≠ t) (n : ℕ) :
    involutionGenerator s * escape t s n ≠ 1 := by
  intro h
  have := congrArg (dihedralMap t s) h
  rw [map_mul, dihedralMap_escape t s hst, dihedralMap_s t s hst, map_one, DihedralGroup.one_def,
    DihedralGroup.sr_mul_sr] at this
  have h2 := DihedralGroup.r.inj this
  have h3 : (-(n : ℤ)) - 1 = 0 := h2
  omega

theorem escape_succ {d : ℕ} (t s : Fin d) (n : ℕ) :
    escape t s (n + 1) = involutionGenerator t * (involutionGenerator s * escape t s n) := by
  simp only [escape, pow_succ', mul_assoc]

/-- Renaming of the free product induced by a permutation of the generators. -/
def permGen {d : ℕ} (σ : Equiv.Perm (Fin d)) : FreeInvolutions d →* FreeInvolutions d :=
  Monoid.CoprodI.lift fun i =>
    (Monoid.CoprodI.of (M := fun _ : Fin d => Multiplicative (ZMod 2)) (i := σ i))

theorem permGen_gen {d : ℕ} (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    permGen σ (involutionGenerator i) = involutionGenerator (σ i) := by
  simp [permGen, involutionGenerator, Monoid.CoprodI.lift_of]

theorem permGen_injective {d : ℕ} (σ : Equiv.Perm (Fin d)) : Function.Injective (permGen σ) := by
  have h : (permGen σ⁻¹).comp (permGen σ) = MonoidHom.id _ := by
    refine Monoid.CoprodI.ext_hom _ _ fun i => ?_
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, permGen, Monoid.CoprodI.lift_of, MonoidHom.id_apply]
    have key : ∀ j k : Fin d, j = k →
        (Monoid.CoprodI.of (M := fun _ : Fin d => Multiplicative (ZMod 2)) (i := j) x) =
          Monoid.CoprodI.of (i := k) x := by
      rintro j k rfl; rfl
    exact key _ _ (by simp)
  intro x y hxy
  have := congrArg (permGen σ⁻¹) hxy
  simpa [← MonoidHom.comp_apply, h] using this


theorem twoStep_mul_aut {d c : ℕ} (H : Gadget d c) (e : Equiv.Perm (Fin d))
    (he : ∀ a b, H.edges (e a) (e b) = H.edges a b) (a b : Fin d) :
    (H.edges * H.edges) (e a) (e b) = (H.edges * H.edges) a b := by
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp e]
  simp only [he]

theorem exists_twoStep_adj {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hg : Good H) (t : Fin d) :
    ∃ s, (twoStepGraph H).Adj t s := by
  by_contra hno
  push Not at hno
  have hall : ∀ v w, ¬ (twoStepGraph H).Adj v w := by
    intro v w hvw
    obtain ⟨e, he1, he2⟩ := hg.1 t v
    apply hno (e.symm w)
    refine ⟨fun h => hvw.1 ?_, ?_⟩
    · rw [← he1, h, Equiv.apply_symm_apply]
    · have := hvw.2
      rw [← he1, ← Equiv.apply_symm_apply e w, twoStep_mul_aut H e he2] at this
      exact this
  have hinj : Function.Injective (twoStepGraph H).connectedComponentMk := by
    intro v w h
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.eq.mp h
    cases p with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (hall _ _)
  have : Finite (twoStepGraph H).ConnectedComponent :=
    Finite.of_surjective (twoStepGraph H).connectedComponentMk (fun c => by
      induction c using SimpleGraph.ConnectedComponent.ind with
      | h v => exact ⟨v, rfl⟩)
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 := hg.2
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  omega

theorem matchingKernel_pos {d c : ℕ} (H : Gadget d c) (x y : Vtx d) (r : Fin d)
    (h1 : 0 < H.edges x.1 r) (h2 : 0 < H.edges r y.1) (h3 : involutionGenerator r * x.2 = y.2) :
    0 < matchingKernel H x y := by
  classical
  unfold matchingKernel
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun s => if involutionGenerator s * x.2 = y.2
    then H.edges x.1 s * H.edges s y.1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r))
  simp only [h3, if_true]
  exact Nat.mul_pos h1 h2

theorem matchingKernel_permGen {d c : ℕ} (H : Gadget d c) (σ : Equiv.Perm (Fin d))
    (hσ : ∀ a b, H.edges (σ a) (σ b) = H.edges a b) (h : FreeInvolutions d) (x y : Vtx d) :
    matchingKernel H x y ≤
      matchingKernel H (σ x.1, permGen σ x.2 * h) (σ y.1, permGen σ y.2 * h) := by
  classical
  unfold matchingKernel
  refine le_of_le_of_eq (Finset.sum_le_sum fun r _ => ?_) (Equiv.sum_comp σ (fun r =>
    if involutionGenerator r * (permGen σ x.2 * h) = permGen σ y.2 * h
    then H.edges (σ x.1) r * H.edges r (σ y.1) else 0))
  by_cases hr : involutionGenerator r * x.2 = y.2
  · have h' : involutionGenerator (σ r) * (permGen σ x.2 * h) = permGen σ y.2 * h := by
      rw [← mul_assoc, ← permGen_gen, ← map_mul, hr]
    simp only [hr, h', if_true, hσ, le_refl]
  · simp only [hr, if_false]
    exact Nat.zero_le _

theorem escape_mem {d c : ℕ} (H : Gadget d c) (a t s j : Fin d) (hst : s ≠ t)
    (htj : 0 < H.edges t j) (hjs : 0 < H.edges j s) (n : ℕ) :
    (j, escape t s n) ∈ truncationVertices H a t := by
  classical
  have hjt : 0 < H.edges j t := by rw [edges_symm]; exact htj
  have hsj : 0 < H.edges s j := by rw [edges_symm]; exact hjs
  induction n with
  | zero =>
    refine Relation.ReflTransGen.single ?_
    have : escape t s 0 = involutionGenerator t := by simp [escape]
    rw [this]
    unfold truncatedKernel
    simpa using htj
  | succ n ih =>
    have hw := escape_ne_one t s hst n
    have hsw := gen_mul_escape_ne_one t s hst n
    have hw' := escape_ne_one t s hst (n + 1)
    refine Relation.ReflTransGen.tail (Relation.ReflTransGen.tail ih (c := (j, involutionGenerator s * escape t s n)) ?_) ?_
    · rw [truncatedKernel_eq_of_ne_one H a t _ _ hw hsw]
      exact matchingKernel_pos H _ _ s hjs hsj rfl
    · rw [truncatedKernel_eq_of_ne_one H a t _ _ hsw hw', escape_succ]
      exact matchingKernel_pos H _ _ t hjt htj rfl

/-- The main combinatorial step: a finite set connected in the full graph embeds into the root
component, by an injective map that does not decrease the kernel. -/
theorem embed_connected {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d)
    (hg : Good H) (a t : Fin d)
    (S : Finset (Vtx d)) (p0 : Vtx d)
    (hconn : ∀ x ∈ S, Relation.ReflTransGen
      (fun u v => u ∈ S ∧ v ∈ S ∧ 0 < matchingKernel H u v) p0 x) :
    ∃ Φ : Vtx d → Vtx d, Set.InjOn Φ S ∧ (∀ x ∈ S, Φ x ∈ truncationVertices H a t) ∧
      ∀ x ∈ S, ∀ y ∈ S, matchingKernel H x y ≤ truncatedKernel H a t (Φ x) (Φ y) := by
  classical
  obtain ⟨s, hs⟩ := exists_twoStep_adj H hd hg t
  have hst : s ≠ t := fun h => hs.1 h.symm
  have hpos := hs.2
  rw [Matrix.mul_apply] at hpos
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  obtain ⟨htj, hjs⟩ := mul_ne_zero_iff.mp hj
  obtain ⟨σ, hσ1, hσ2⟩ := hg.1 p0.1 j
  set z : Vtx d → FreeInvolutions d := fun x => (permGen σ x.2 * (permGen σ p0.2)⁻¹)⁻¹
  have hfin : (escape t s ⁻¹' ((S.image z : Finset _) : Set (FreeInvolutions d))).Finite :=
    Set.Finite.preimage (escape_injective t s hst).injOn (S.image z).finite_toSet
  obtain ⟨n, hn⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_preimage, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, not_exists, not_and] at hn
  set h := (permGen σ p0.2)⁻¹ * escape t s n
  set Φ : Vtx d → Vtx d := fun x => (σ x.1, permGen σ x.2 * h) with hΦ
  have hne : ∀ x ∈ S, (Φ x).2 ≠ 1 := by
    intro x hx heq
    apply hn x hx
    simp only [hΦ, h, ← mul_assoc] at heq
    exact (eq_inv_of_mul_eq_one_right heq).symm
  have hp0 : Φ p0 = (j, escape t s n) := by
    simp only [hΦ, h, mul_inv_cancel_left, hσ1]
  have hK : ∀ x ∈ S, ∀ y ∈ S, matchingKernel H x y ≤ truncatedKernel H a t (Φ x) (Φ y) := by
    intro x hx y hy
    rw [truncatedKernel_eq_of_ne_one H a t _ _ (hne x hx) (hne y hy)]
    exact matchingKernel_permGen H σ hσ2 h x y
  refine ⟨Φ, ?_, ?_, hK⟩
  · intro x _ y _ hxy
    simp only [hΦ, Prod.mk.injEq, mul_left_inj] at hxy
    exact Prod.ext (σ.injective hxy.1) (permGen_injective σ hxy.2)
  · intro x hx
    have hpath := hconn x hx
    induction hpath with
    | refl =>
      rw [hp0]
      exact escape_mem H a t s j hst (Nat.pos_of_ne_zero htj) (Nat.pos_of_ne_zero hjs) n
    | tail _ hbc ih =>
      obtain ⟨hb, hc', hpos'⟩ := hbc
      exact Relation.ReflTransGen.tail (ih hb) (lt_of_lt_of_le hpos' (hK _ hb _ hc'))

theorem comb_bound {d c : ℕ} (H : Gadget d c) (μ : ℝ)
    (hE : ∀ (S : Finset (Vtx d)) (p0 : Vtx d), (∀ x ∈ S, Relation.ReflTransGen
      (fun u v => u ∈ S ∧ v ∈ S ∧ 0 < matchingKernel H u v) p0 x) →
      ∀ f : Vtx d → ℝ, (∀ x, 0 ≤ f x) →
      ∑ x ∈ S, ∑ y ∈ S, f x * f y * (matchingKernel H x y : ℝ) ≤ μ * ∑ x ∈ S, f x ^ 2) :
    ∀ (n : ℕ) (S : Finset (Vtx d)), S.card = n → ∀ f : Vtx d → ℝ, (∀ x, 0 ≤ f x) →
      ∑ x ∈ S, ∑ y ∈ S, f x * f y * (matchingKernel H x y : ℝ) ≤ μ * ∑ x ∈ S, f x ^ 2 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS f hf
  rcases S.eq_empty_or_nonempty with h0 | ⟨p0, hp0⟩
  · subst h0; simp
  set R := fun u v => u ∈ S ∧ v ∈ S ∧ 0 < matchingKernel H u v
  set P := fun x => Relation.ReflTransGen R p0 x
  by_cases hall : ∀ x ∈ S, P x
  · exact hE S p0 hall f hf
  push Not at hall
  obtain ⟨q, hqS, hq⟩ := hall
  set S1 := S.filter P
  set S2 := S.filter (fun x => ¬ P x)
  have hcross : ∀ x ∈ S1, ∀ y ∈ S2, matchingKernel H x y = 0 := by
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    by_contra hne
    exact hy.2 (hx.2.tail ⟨hx.1, hy.1, Nat.pos_of_ne_zero hne⟩)
  have hcross' : ∀ x ∈ S2, ∀ y ∈ S1, matchingKernel H x y = 0 := by
    intro x hx y hy
    rw [matchingKernel_symm]; exact hcross y hy x hx
  have hc1 : S1.card < n := by
    rw [← hS]
    refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have := h hqS
    rw [Finset.mem_filter] at this
    exact hq this.2
  have hc2 : S2.card < n := by
    rw [← hS]
    refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have := h hp0
    rw [Finset.mem_filter] at this
    exact this.2 Relation.ReflTransGen.refl
  have i1 := ih _ hc1 S1 rfl f hf
  have i2 := ih _ hc2 S2 rfl f hf
  have split : ∀ g : Vtx d → ℝ, ∑ x ∈ S, g x = ∑ x ∈ S1, g x + ∑ x ∈ S2, g x :=
    fun g => (Finset.sum_filter_add_sum_filter_not S P g).symm
  rw [split, split (fun x => f x ^ 2), mul_add]
  simp only [split (fun y => _ * f y * _)]
  have z1 : ∑ x ∈ S1, ∑ y ∈ S2, f x * f y * (matchingKernel H x y : ℝ) = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => by simp [hcross x hx y hy]
  have z2 : ∑ x ∈ S2, ∑ y ∈ S1, f x * f y * (matchingKernel H x y : ℝ) = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => by simp [hcross' x hx y hy]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, z1, z2]
  linarith

theorem topEdge_le_truncated {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hc : 2 ≤ c)
    (hg : Good H) (a t : Fin d) (hat : 0 < H.edges a t) :
    topEdge (matchingLimit H) ≤ topEdge (truncatedAdj H a t) := by
  have := nontrivial_treeClouds (d := d) (by omega)
  set μ := topEdge (truncatedAdj H a t)
  have hE : ∀ (S : Finset (Vtx d)) (p0 : Vtx d), (∀ x ∈ S, Relation.ReflTransGen
      (fun u v => u ∈ S ∧ v ∈ S ∧ 0 < matchingKernel H u v) p0 x) →
      ∀ f : Vtx d → ℝ, (∀ x, 0 ≤ f x) →
      ∑ x ∈ S, ∑ y ∈ S, f x * f y * (matchingKernel H x y : ℝ) ≤ μ * ∑ x ∈ S, f x ^ 2 := by
    intro S p0 hconn f hf
    obtain ⟨Φ, hΦ, hX, hK⟩ := embed_connected H hd hg a t S p0 hconn
    refine le_trans (Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_)
      (rayleigh_on_component H a t S Φ hΦ hX f)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hK x hx y hy) (mul_nonneg (hf x) (hf y))
  have hcomb := comb_bound H μ hE
  rw [topEdge_le_iff _ (matchingLimit_selfAdjoint H)]
  refine rayleigh_bound_of_finite _ _ fun S c => ?_
  refine (re_inner_sum_delta_le _ _ (matchingLimit_coord H) S c).trans ?_
  have e3 := norm_sq_sum_delta S id c (Set.injOn_id _)
  simp only [id] at e3
  rw [e3]
  exact hcomb _ S rfl (fun x => ‖c x‖) (fun x => norm_nonneg _)

theorem finite_truncation_main {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hc : 2 ≤ c)
  (hg : Good H) (a t : Fin d) (hat : 0 < H.edges a t) :
  topEdge (truncatedAdj H a t) = topEdge (matchingLimit H) :=
  le_antisymm (topEdge_truncated_le H hd a t hat) (topEdge_le_truncated H hd hc hg a t hat)

end ZigZagStrong.ZigZag

open ZigZagStrong.ZigZag in
theorem solution {d c : ℕ} (H : Gadget d c) (hd : 3 ≤ d) (hc : 2 ≤ c)
  (hg : Good H) (a t : Fin d) (hat : 0 < H.edges a t) :
  topEdge (truncatedAdj H a t) = topEdge (matchingLimit H) :=
  finite_truncation_main H hd hc hg a t hat

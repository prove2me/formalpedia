-- Prove2me | solution 1 for ObjectCentric.inferred_slot_meets_one_object
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T18:39:58.913431+00:00
-- url     : https://prove2.me/submissions/4f02caee-027b-4486-988c-5c78c00947af

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

lemma oc_inj {K M N : ℕ} (X : Set (Obs N)) (f : Lat K M → Obs N) (g : Obs N → Lat K M)
    (hf : IsDiffeoWithInv f g X) (z : Lat K M) : Function.Injective (fderiv ℝ f z) := by
  obtain ⟨hfc, hgc, hr, hgf⟩ := hf
  have hfd : HasFDerivAt f (fderiv ℝ f z) z :=
    (hfc.differentiable one_ne_zero z).hasFDerivAt
  have hmem : f z ∈ X := hr ▸ ⟨z, rfl⟩
  have hgd : HasFDerivWithinAt g (fderivWithin ℝ g X (f z)) X (f z) :=
    ((hgc.differentiableOn one_ne_zero) (f z) hmem).hasFDerivWithinAt
  have hcomp := hgd.comp_hasFDerivAt z hfd (Filter.Eventually.of_forall fun x => hr ▸ ⟨x, rfl⟩)
  have hid : g ∘ f = id := funext hgf
  rw [hid] at hcomp
  have huniq := hcomp.unique (hasFDerivAt_id z)
  intro u v huv
  have := congrArg (fun L => L u) huniq
  have h2 := congrArg (fun L => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
  rw [← this, ← h2, huv]

end ObjectCentric

open ObjectCentric in
theorem oc_rank {K M N : ℕ} (hM : 0 < M)
    (X : Set (Obs N)) (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) :
    ∀ (z : Lat K M) (k : Fin K), subRank f z (indexSet f z k) = M := by
  intro z k
  classical
  set S := indexSet f z k with hS
  set J := jac f z with hJ
  set A := J.submatrix (fun n : S => (n : Fin N)) id with hA
  set B : Matrix S (Fin M) ℝ := Matrix.of fun n m => A n (k, m) with hB
  set E : Matrix (Fin M) (Fin K × Fin M) ℝ := Matrix.of fun m c => if c.1 = k ∧ c.2 = m then 1 else 0 with hE
  set E' : Matrix (Fin K × Fin M) (Fin M) ℝ := Matrix.of fun c m => if c.1 = k ∧ c.2 = m then 1 else 0 with hE'
  have hzero : ∀ n : S, ∀ j m, j ≠ k → A n (j, m) = 0 := by
    intro n j m hjk
    have hn : (n : Fin N) ∈ indexSet f z k := n.2
    have hnj : (n : Fin N) ∉ indexSet f z j := fun h =>
      Set.disjoint_left.mp (hfc z k j (Ne.symm hjk)) hn h
    simp only [indexSet, Set.mem_ofPred_eq, not_not] at hnj
    have := congrFun hnj m
    simpa [slotGrad, hA, hJ] using this
  have hAB : A = B * E := by
    ext n ⟨j, m'⟩
    rw [Matrix.mul_apply]; simp only [hB, hE, Matrix.of_apply]
    by_cases hjk : j = k
    · subst hjk
      rw [Finset.sum_eq_single m']
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · rw [hzero n j m' hjk]
      simp [hjk]
  have hBA : B = A * E' := by
    ext n m
    rw [Matrix.mul_apply]; simp only [hB, hE', Matrix.of_apply]
    rw [Finset.sum_eq_single (k, m)]
    · simp
    · rintro ⟨j, m'⟩ _ hb
      by_cases h : j = k ∧ m' = m
      · exact absurd (by rw [h.1, h.2]) hb
      · simp [h]
    · simp
  have hinj : Function.Injective B.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ n : S, ∑ m, B n m * v m = 0 := fun n => by
      have := congrFun hv n
      simpa [Matrix.mulVec, dotProduct] using this
    set w : Lat K M := Pi.single k v with hw
    have hwsum : w = ∑ m, v m • (Pi.single k (Pi.single m (1 : ℝ)) : Lat K M) := by
      funext j m
      rw [Finset.sum_apply, Finset.sum_apply]
      simp only [hw, Pi.smul_apply, smul_eq_mul]
      by_cases hj : j = k
      · subst hj; simp [Pi.single_apply]
      · simp [hj]
    have hDw : fderiv ℝ f z w = 0 := by
      funext n
      rw [hwsum, map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases hn : n ∈ S
      · have := hv' ⟨n, hn⟩
        simpa [hB, hA, hJ, jac, mul_comm, Matrix.of_apply] using this
      · have hn' : slotGrad f z n k = 0 := by
          simpa [hS, indexSet] using hn
        refine Finset.sum_eq_zero fun m _ => ?_
        have := congrFun hn' m
        simp only [slotGrad, jac, Pi.zero_apply] at this
        rw [this, mul_zero]
    have hw0 : w = 0 := oc_inj X f g hf z (by rw [hDw, map_zero])
    funext m
    have := congrFun (congrFun hw0 k) m
    simpa [hw] using this
  have hrB : B.rank = M := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj]; simp
  have h1 : A.rank ≤ M := by
    rw [hAB]; exact (Matrix.rank_mul_le_left _ _).trans hrB.le
  have h2 : M ≤ A.rank := by
    calc M = B.rank := hrB.symm
      _ ≤ A.rank := by rw [hBA]; exact Matrix.rank_mul_le_left _ _
  show A.rank = M
  omega


namespace ObjectCentric

lemma om_dec {K M : ℕ} (w : Lat K M) :
    w = ∑ c : Fin K × Fin M, w c.1 c.2 • (Pi.single c.1 (Pi.single c.2 1) : Lat K M) := by
  funext k m
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_apply, Pi.single_apply, ite_apply, Finset.sum_ite_eq]

/-- coefficient matrix of a linear endomorphism of `Lat`. -/
def omMat {K M : ℕ} (H : Lat K M →L[ℝ] Lat K M) : Matrix (Fin K × Fin M) (Fin K × Fin M) ℝ :=
  fun c' c => H (Pi.single c.1 (Pi.single c.2 1)) c'.1 c'.2

lemma om_jac {K M N : ℕ} (f fh : Lat K M → Obs N) (z w : Lat K M) (H : Lat K M →L[ℝ] Lat K M)
    (hL : fderiv ℝ f z = (fderiv ℝ fh w).comp H) : jac f z = jac fh w * omMat H := by
  ext n c
  simp only [jac, Matrix.mul_apply, omMat, hL, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [om_dec (H (Pi.single c.1 (Pi.single c.2 1)))]
  simp [map_sum, map_smul, Finset.sum_apply, mul_comm]

lemma om_inv {K M : ℕ} (H G : Lat K M →L[ℝ] Lat K M) (h : H.comp G = ContinuousLinearMap.id ℝ _) :
    omMat H * omMat G = 1 := by
  ext c' c
  simp only [Matrix.mul_apply, omMat]
  have := congrArg (fun L => L (Pi.single c.1 (Pi.single c.2 1) : Lat K M)) h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  conv at this => lhs; rw [om_dec (G (Pi.single c.1 (Pi.single c.2 1)))]
  have h2 := congrFun (congrFun this c'.1) c'.2
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  rw [Matrix.one_apply]
  convert h2 using 1
  · exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · obtain ⟨k, m⟩ := c; obtain ⟨k', m'⟩ := c'
    by_cases hk : k' = k
    · subst hk; by_cases hm : m' = m
      · subst hm; simp
      · simp [hm, Pi.single_apply]
    · simp [hk, Pi.single_apply]

end ObjectCentric

open ObjectCentric in
theorem om_main {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) :
    ∀ (z : Lat K M) (i : Fin K), ∃! j : Fin K,
      (indexSet fhat (ghat (f z)) j ∩ indexSet f z i).Nonempty := by
  intro z i
  classical
  obtain ⟨hfc1, hgc1, hr, hgf⟩ := hf
  obtain ⟨hfh1, hgh1, hrh, hgfh⟩ := hhat
  set zh := ghat (f z) with hzh
  -- basic identities
  have hfX : ∀ w, f w ∈ X := fun w => hr ▸ ⟨w, rfl⟩
  have hfhX : ∀ w, fhat w ∈ X := fun w => hrh ▸ ⟨w, rfl⟩
  have hfhg : ∀ x ∈ X, fhat (ghat x) = x := by
    intro x hx; rw [← hrh] at hx; obtain ⟨w, rfl⟩ := hx; rw [hgfh]
  have hfg : ∀ x ∈ X, f (g x) = x := by
    intro x hx; rw [← hr] at hx; obtain ⟨w, rfl⟩ := hx; rw [hgf]
  -- derivatives
  have hfd : ∀ w, HasFDerivAt f (fderiv ℝ f w) w := fun w =>
    (hfc1.differentiable one_ne_zero w).hasFDerivAt
  have hfhd : ∀ w, HasFDerivAt fhat (fderiv ℝ fhat w) w := fun w =>
    (hfh1.differentiable one_ne_zero w).hasFDerivAt
  have hghd : HasFDerivWithinAt ghat (fderivWithin ℝ ghat X (f z)) X (f z) :=
    ((hgh1.differentiableOn one_ne_zero) (f z) (hfX z)).hasFDerivWithinAt
  set H := (fderivWithin ℝ ghat X (f z)).comp (fderiv ℝ f z) with hH
  have hHd : HasFDerivAt (ghat ∘ f) H z :=
    hghd.comp_hasFDerivAt z (hfd z) (Filter.Eventually.of_forall hfX)
  have hfeq : fhat ∘ (ghat ∘ f) = f := funext fun w => hfhg _ (hfX w)
  have hL : fderiv ℝ f z = (fderiv ℝ fhat zh).comp H := by
    have h1 := (hfhd zh).comp z hHd
    rw [hfeq] at h1
    exact h1.fderiv
  have hzk : g (fhat zh) = z := by rw [hzh, hfhg _ (hfX z), hgf]
  have hgd : HasFDerivWithinAt g (fderivWithin ℝ g X (fhat zh)) X (fhat zh) :=
    ((hgc1.differentiableOn one_ne_zero) (fhat zh) (hfhX zh)).hasFDerivWithinAt
  set G := (fderivWithin ℝ g X (fhat zh)).comp (fderiv ℝ fhat zh) with hG
  have hGd : HasFDerivAt (g ∘ fhat) G zh :=
    hgd.comp_hasFDerivAt zh (hfhd zh) (Filter.Eventually.of_forall hfhX)
  have hHG : H.comp G = ContinuousLinearMap.id ℝ _ := by
    have hHd' : HasFDerivAt (ghat ∘ f) H ((g ∘ fhat) zh) := by
      simp only [Function.comp_apply]; rw [hzk]; exact hHd
    have h1 := hHd'.comp zh hGd
    have hid : (ghat ∘ f) ∘ (g ∘ fhat) = id := funext fun w => by
      simp only [Function.comp_apply, id]; rw [hfg _ (hfhX w), hgfh]
    rw [hid] at h1
    exact h1.unique (hasFDerivAt_id zh)
  set Hm := omMat H
  set Gm := omMat G
  have hHGm : Hm * Gm = 1 := om_inv H G hHG
  have hJ : jac f z = jac fhat zh * Hm := om_jac f fhat z zh H hL
  have hrow : ∀ n, jac f z n = Matrix.vecMul (jac fhat zh n) Hm := by
    intro n; rw [hJ]; ext c; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  -- membership in index sets via rows
  have hmem : ∀ (F : Lat K M → Obs N) (w : Lat K M) (n : Fin N) (k : Fin K),
      n ∈ indexSet F w k ↔ ∃ m, jac F w n (k, m) ≠ 0 := by
    intro F w n k
    simp only [indexSet, Set.mem_setOf_eq, slotGrad, ne_eq, funext_iff, Pi.zero_apply, not_forall]
  -- I_i nonempty
  have hne : (indexSet f z i).Nonempty := by
    have hinj : Function.Injective (fderiv ℝ f z) := by
      have hcomp := hghd.comp_hasFDerivAt z (hfd z) (Filter.Eventually.of_forall hfX)
      have hid : g ∘ f = id := funext hgf
      have hgd0 : HasFDerivWithinAt g (fderivWithin ℝ g X (f z)) X (f z) :=
        ((hgc1.differentiableOn one_ne_zero) (f z) (hfX z)).hasFDerivWithinAt
      have hc2 := hgd0.comp_hasFDerivAt z (hfd z) (Filter.Eventually.of_forall hfX)
      rw [hid] at hc2
      have huniq := hc2.unique (hasFDerivAt_id z)
      intro u v huv
      have e1 := congrArg (fun L => L u) huniq
      have e2 := congrArg (fun L => L v) huniq
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e1 e2
      rw [← e1, ← e2, huv]
    set m0 : Fin M := ⟨0, hM⟩
    have hv : (Pi.single i (Pi.single m0 1) : Lat K M) ≠ 0 := by
      intro h; have := congrFun (congrFun h i) m0; simp at this
    have hLv : fderiv ℝ f z (Pi.single i (Pi.single m0 1)) ≠ 0 := by
      intro h; exact hv (hinj (by rw [h, map_zero]))
    obtain ⟨n, hn⟩ := Function.ne_iff.1 hLv
    exact ⟨n, (hmem f z n i).2 ⟨m0, hn⟩⟩
  -- each n in I_i lies in some inferred index set
  have hsome : ∀ n ∈ indexSet f z i, ∃ j, n ∈ indexSet fhat zh j := by
    intro n hn
    obtain ⟨m, hm⟩ := (hmem f z n i).1 hn
    have : jac fhat zh n ≠ 0 := by
      intro h0; apply hm; rw [hrow, h0]; simp
    obtain ⟨⟨j, m'⟩, hj⟩ := Function.ne_iff.1 this
    exact ⟨j, (hmem fhat zh n j).2 ⟨m', hj⟩⟩
  obtain ⟨n0, hn0⟩ := hne
  obtain ⟨j0, hj0⟩ := hsome n0 hn0
  refine ⟨j0, ⟨n0, hj0, hn0⟩, ?_⟩
  -- uniqueness
  intro j ⟨n1, hn1j, hn1i⟩
  by_contra hjj
  -- partition I_i into S1 = I_i ∩ Ĩ_j and S2 = I_i \ Ĩ_j
  set S1 := indexSet f z i ∩ indexSet fhat zh j
  set S2 := indexSet f z i \ indexSet fhat zh j
  have hS1 : S1.Nonempty := ⟨n1, hn1i, hn1j⟩
  have hS2 : S2.Nonempty := ⟨n0, hn0, fun h =>
    Set.disjoint_left.mp (hfhatc zh j0 j (Ne.symm hjj)) hj0 h⟩
  have hdisj : Disjoint S1 S2 := Set.disjoint_left.mpr fun n h1 h2 => h2.2 h1.2
  have hunion : S1 ∪ S2 = indexSet f z i := Set.inter_union_sdiff _ _
  have hdep := hfi z i S1 S2 hS1 hS2 hdisj hunion
  -- linear algebra
  let P : ((Fin K × Fin M) → ℝ) →ₗ[ℝ] ((Fin K × Fin M) → ℝ) :=
    { toFun := fun r c => if c.1 = j then r c else 0
      map_add' := fun r s => by funext c; by_cases hc : c.1 = j <;> simp [hc]
      map_smul' := fun a r => by funext c; by_cases hc : c.1 = j <;> simp [hc] }
  let Vh := Matrix.vecMulLinear Hm
  let Vg := Matrix.vecMulLinear Gm
  let Q := P ∘ₗ Vg
  have hVgVh : ∀ r, Vg (Vh r) = r := fun r => by
    simp [Vg, Vh, Matrix.vecMul_vecMul, hHGm]
  have hrow1 : ∀ n ∈ S1, P (jac fhat zh n) = jac fhat zh n := by
    intro n hn
    funext c
    show (if c.1 = j then _ else _) = _
    split_ifs with hc
    · rfl
    · have hn' : n ∉ indexSet fhat zh c.1 := fun h =>
        Set.disjoint_left.mp (hfhatc zh j c.1 (Ne.symm hc)) hn.2 h
      rw [hmem] at hn'; push_neg at hn'
      exact (hn' c.2).symm
  have hrow2 : ∀ n ∈ S2, P (jac fhat zh n) = 0 := by
    intro n hn
    funext c
    show (if c.1 = j then _ else _) = _
    split_ifs with hc
    · have hn' := hn.2; rw [hmem] at hn'; push_neg at hn'
      have := hn' c.2; rw [← hc] at this; exact this
    · rfl
  let A1 := LinearMap.ker (Vh ∘ₗ Q - LinearMap.id)
  let A2 := LinearMap.ker Q
  have hA : Disjoint A1 A2 := by
    rw [Submodule.disjoint_def]
    intro s h1 h2
    simp only [A1, A2, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, sub_eq_zero] at h1 h2
    rw [h2, map_zero] at h1; exact h1.symm
  let rows : Fin N → (Fin K × Fin M → ℝ) := fun n => jac f z n
  set R := fun S : Set (Fin N) => Submodule.span ℝ (rows '' S)
  have hR1 : R S1 ≤ A1 := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    simp only [SetLike.mem_coe, A1, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, sub_eq_zero, Q]
    show Vh (P (Vg (jac f z n))) = jac f z n
    rw [hrow n]
    show Vh (P (Vg (Vh (jac fhat zh n)))) = Vh (jac fhat zh n)
    rw [hVgVh, hrow1 n hn]
  have hR2 : R S2 ≤ A2 := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    simp only [SetLike.mem_coe, A2, LinearMap.mem_ker, Q, LinearMap.comp_apply]
    show P (Vg (jac f z n)) = 0
    rw [hrow n]
    show P (Vg (Vh (jac fhat zh n))) = 0
    rw [hVgVh, hrow2 n hn]
  have hrank : ∀ S : Set (Fin N), subRank f z S = Module.finrank ℝ (R S) := by
    intro S
    unfold subRank
    rw [Matrix.rank_eq_finrank_span_row]
    have hset : Set.range ((jac f z).submatrix (fun n : S => (n : Fin N)) id).row = rows '' S := by
      ext v; constructor
      · rintro ⟨n, rfl⟩; exact ⟨n, n.2, by ext; rfl⟩
      · rintro ⟨n, hn, rfl⟩; exact ⟨⟨n, hn⟩, by ext; rfl⟩
    rw [hset]
  have hRU : R (S1 ∪ S2) = R S1 ⊔ R S2 := by
    show Submodule.span ℝ (rows '' (S1 ∪ S2)) = Submodule.span ℝ (rows '' S1) ⊔ Submodule.span ℝ (rows '' S2)
    rw [Set.image_union, Submodule.span_union]
  have hinf : R S1 ⊓ R S2 = ⊥ := (hA.mono hR1 hR2).eq_bot
  have key := Submodule.finrank_sup_add_finrank_inf_eq (R S1) (R S2)
  rw [hinf, finrank_bot, add_zero] at key
  unfold SubmechDependent at hdep
  rw [hrank, hrank, hrank, hRU, key] at hdep
  exact lt_irrefl _ hdep


open ObjectCentric in
theorem solution {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) :
    ∀ (z : Lat K M) (j : Fin K), ∃! i : Fin K,
      (indexSet fhat (ghat (f z)) j ∩ indexSet f z i).Nonempty := by
  intro z j
  classical
  have hOM := om_main hM X f g hf hfc hfi ghat fhat hhat hfhatc z
  have hrk : ∀ k, subRank f z (indexSet f z k) = M := oc_rank hM X f g hf hfc z
  have hf' := hf
  have hhat' := hhat
  obtain ⟨hfc1, hgc1, hr, hgf⟩ := hf
  obtain ⟨hfh1, hgh1, hrh, hgfh⟩ := hhat
  set zh := ghat (f z) with hzh
  have hfX : ∀ w, f w ∈ X := fun w => hr ▸ ⟨w, rfl⟩
  have hfhX : ∀ w, fhat w ∈ X := fun w => hrh ▸ ⟨w, rfl⟩
  have hfhg : ∀ x ∈ X, fhat (ghat x) = x := by
    intro x hx; rw [← hrh] at hx; obtain ⟨w, rfl⟩ := hx; rw [hgfh]
  have hfg : ∀ x ∈ X, f (g x) = x := by
    intro x hx; rw [← hr] at hx; obtain ⟨w, rfl⟩ := hx; rw [hgf]
  have hfd : ∀ w, HasFDerivAt f (fderiv ℝ f w) w := fun w =>
    (hfc1.differentiable one_ne_zero w).hasFDerivAt
  have hfhd : ∀ w, HasFDerivAt fhat (fderiv ℝ fhat w) w := fun w =>
    (hfh1.differentiable one_ne_zero w).hasFDerivAt
  have hghd : HasFDerivWithinAt ghat (fderivWithin ℝ ghat X (f z)) X (f z) :=
    ((hgh1.differentiableOn one_ne_zero) (f z) (hfX z)).hasFDerivWithinAt
  set H := (fderivWithin ℝ ghat X (f z)).comp (fderiv ℝ f z) with hH
  have hHd : HasFDerivAt (ghat ∘ f) H z :=
    hghd.comp_hasFDerivAt z (hfd z) (Filter.Eventually.of_forall hfX)
  have hfeq : fhat ∘ (ghat ∘ f) = f := funext fun w => hfhg _ (hfX w)
  have hL : fderiv ℝ f z = (fderiv ℝ fhat zh).comp H := by
    have h1 := (hfhd zh).comp z hHd
    rw [hfeq] at h1
    exact h1.fderiv
  have hzk : g (fhat zh) = z := by rw [hzh, hfhg _ (hfX z), hgf]
  have hgd : HasFDerivWithinAt g (fderivWithin ℝ g X (fhat zh)) X (fhat zh) :=
    ((hgc1.differentiableOn one_ne_zero) (fhat zh) (hfhX zh)).hasFDerivWithinAt
  set G := (fderivWithin ℝ g X (fhat zh)).comp (fderiv ℝ fhat zh) with hG
  have hGd : HasFDerivAt (g ∘ fhat) G zh :=
    hgd.comp_hasFDerivAt zh (hfhd zh) (Filter.Eventually.of_forall hfhX)
  have hfeq2 : f ∘ (g ∘ fhat) = fhat := funext fun w => hfg _ (hfhX w)
  have hL2 : fderiv ℝ fhat zh = (fderiv ℝ f z).comp G := by
    have hfz : HasFDerivAt f (fderiv ℝ f z) ((g ∘ fhat) zh) := by
      simp only [Function.comp_apply]; rw [hzk]; exact hfd z
    have h1 := hfz.comp zh hGd
    rw [hfeq2] at h1
    exact h1.fderiv
  set Hm := omMat H
  have hJ : jac f z = jac fhat zh * Hm := om_jac f fhat z zh H hL
  have hJ2 : jac fhat zh = jac f z * omMat G := om_jac fhat f zh z G hL2
  have hrow : ∀ n, jac f z n = Matrix.vecMul (jac fhat zh n) Hm := by
    intro n; rw [hJ]; ext c; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hrow2 : ∀ n, jac fhat zh n = Matrix.vecMul (jac f z n) (omMat G) := by
    intro n; rw [hJ2]; ext c; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hmem : ∀ (F : Lat K M → Obs N) (w : Lat K M) (n : Fin N) (k : Fin K),
      n ∈ indexSet F w k ↔ ∃ m, jac F w n (k, m) ≠ 0 := by
    intro F w n k
    simp only [indexSet, Set.mem_setOf_eq, slotGrad, ne_eq, funext_iff, Pi.zero_apply, not_forall]
  -- Ĩ_j nonempty
  have hne : (indexSet fhat zh j).Nonempty := by
    have hinj : Function.Injective (fderiv ℝ fhat zh) := by
      have hc2 := hghd.comp_hasFDerivAt z (hfd z) (Filter.Eventually.of_forall hfX)
      have hgd0 : HasFDerivWithinAt ghat (fderivWithin ℝ ghat X (fhat zh)) X (fhat zh) :=
        ((hgh1.differentiableOn one_ne_zero) (fhat zh) (hfhX zh)).hasFDerivWithinAt
      have hc3 := hgd0.comp_hasFDerivAt zh (hfhd zh) (Filter.Eventually.of_forall hfhX)
      have hid : ghat ∘ fhat = id := funext hgfh
      rw [hid] at hc3
      have huniq := hc3.unique (hasFDerivAt_id zh)
      intro u v huv
      have e1 := congrArg (fun L => L u) huniq
      have e2 := congrArg (fun L => L v) huniq
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e1 e2
      rw [← e1, ← e2, huv]
    set m0 : Fin M := ⟨0, hM⟩
    have hv : (Pi.single j (Pi.single m0 1) : Lat K M) ≠ 0 := by
      intro h; have := congrFun (congrFun h j) m0; simp at this
    have hLv : fderiv ℝ fhat zh (Pi.single j (Pi.single m0 1)) ≠ 0 := by
      intro h; exact hv (hinj (by rw [h, map_zero]))
    obtain ⟨n, hn⟩ := Function.ne_iff.1 hLv
    exact ⟨n, (hmem fhat zh n j).2 ⟨m0, hn⟩⟩
  obtain ⟨n0, hn0⟩ := hne
  have hex : ∃ i, n0 ∈ indexSet f z i := by
    obtain ⟨m, hm⟩ := (hmem fhat zh n0 j).1 hn0
    have : jac f z n0 ≠ 0 := by
      intro h0; apply hm; rw [hrow2, h0]; simp
    obtain ⟨⟨i, m'⟩, hi⟩ := Function.ne_iff.1 this
    exact ⟨i, (hmem f z n0 i).2 ⟨m', hi⟩⟩
  obtain ⟨i0, hi0⟩ := hex
  refine ⟨i0, ⟨n0, hn0, hi0⟩, ?_⟩
  intro i ⟨n1, hn1j, hn1i⟩
  by_contra hii
  -- every pixel of I_i or I_i0 lies in Ĩ_j
  have hsub : ∀ k, (indexSet fhat zh j ∩ indexSet f z k).Nonempty →
      ∀ n ∈ indexSet f z k, n ∈ indexSet fhat zh j := by
    intro k hk n hn
    obtain ⟨m, hm⟩ := (hmem f z n k).1 hn
    have : jac fhat zh n ≠ 0 := by
      intro h0; apply hm; rw [hrow, h0]; simp
    obtain ⟨⟨j', m'⟩, hj'⟩ := Function.ne_iff.1 this
    have hnj' : n ∈ indexSet fhat zh j' := (hmem fhat zh n j').2 ⟨m', hj'⟩
    obtain ⟨jj, _, hjj⟩ := hOM k
    have e1 := hjj j hk
    have e2 := hjj j' ⟨n, hnj', hn⟩
    rw [← e1] at e2; rw [← e2]; exact hnj'
  have hs1 := hsub i ⟨n1, hn1j, hn1i⟩
  have hs0 := hsub i0 ⟨n0, hn0, hi0⟩
  -- linear maps
  let rows : Fin N → (Fin K × Fin M → ℝ) := fun n => jac f z n
  set R := fun S : Set (Fin N) => Submodule.span ℝ (rows '' S)
  let Pi_ : ((Fin K × Fin M) → ℝ) →ₗ[ℝ] ((Fin K × Fin M) → ℝ) :=
    { toFun := fun r c => if c.1 = i then r c else 0
      map_add' := fun r s => by funext c; by_cases hc : c.1 = i <;> simp [hc]
      map_smul' := fun a r => by funext c; by_cases hc : c.1 = i <;> simp [hc] }
  let ι : (Fin M → ℝ) →ₗ[ℝ] ((Fin K × Fin M) → ℝ) :=
    { toFun := fun s c => if c.1 = j then s c.2 else 0
      map_add' := fun r s => by funext c; by_cases hc : c.1 = j <;> simp [hc]
      map_smul' := fun a r => by funext c; by_cases hc : c.1 = j <;> simp [hc] }
  let Vh := Matrix.vecMulLinear Hm
  have hRi : R (indexSet f z i) ≤ LinearMap.ker (Pi_ - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    funext c
    show (if c.1 = i then _ else _) = _
    split_ifs with hc
    · rfl
    · have hn' : n ∉ indexSet f z c.1 := fun h =>
        Set.disjoint_left.mp (hfc z i c.1 (Ne.symm hc)) hn h
      rw [hmem] at hn'; push_neg at hn'
      exact (hn' c.2).symm
  have hRi0 : R (indexSet f z i0) ≤ LinearMap.ker Pi_ := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    funext c
    show (if c.1 = i then _ else _) = _
    split_ifs with hc
    · have hn' : n ∉ indexSet f z i := fun h =>
        Set.disjoint_left.mp (hfc z i i0 hii) h hn
      rw [hmem] at hn'; push_neg at hn'
      have := hn' c.2; rw [← hc] at this; exact this
    · rfl
  have hA : Disjoint (LinearMap.ker (Pi_ - LinearMap.id)) (LinearMap.ker Pi_) := by
    rw [Submodule.disjoint_def]
    intro s h1 h2
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h1 h2
    rw [h2] at h1; exact h1.symm
  have hrank : ∀ S : Set (Fin N), subRank f z S = Module.finrank ℝ (R S) := by
    intro S
    unfold subRank
    rw [Matrix.rank_eq_finrank_span_row]
    have hset : Set.range ((jac f z).submatrix (fun n : S => (n : Fin N)) id).row = rows '' S := by
      ext v; constructor
      · rintro ⟨n, rfl⟩; exact ⟨n, n.2, by ext; rfl⟩
      · rintro ⟨n, hn, rfl⟩; exact ⟨⟨n, hn⟩, by ext; rfl⟩
    rw [hset]
  have hinf : R (indexSet f z i) ⊓ R (indexSet f z i0) = ⊥ := (hA.mono hRi hRi0).eq_bot
  have key := Submodule.finrank_sup_add_finrank_inf_eq (R (indexSet f z i)) (R (indexSet f z i0))
  rw [hinf, finrank_bot, add_zero, ← hrank, ← hrank, hrk, hrk] at key
  have hle : R (indexSet f z i) ⊔ R (indexSet f z i0) ≤ LinearMap.range (Vh ∘ₗ ι) := by
    rw [sup_le_iff]
    constructor <;>
    · rw [Submodule.span_le]
      rintro _ ⟨n, hn, rfl⟩
      have hnj : n ∈ indexSet fhat zh j := by first | exact hs1 n hn | exact hs0 n hn
      refine ⟨fun m => jac fhat zh n (j, m), ?_⟩
      show Matrix.vecMul (ι fun m => jac fhat zh n (j, m)) Hm = jac f z n
      rw [hrow n]
      congr 1
      funext c
      show (if c.1 = j then _ else _) = _
      split_ifs with hc
      · rw [← hc]
      · have hn' : n ∉ indexSet fhat zh c.1 := fun h =>
          Set.disjoint_left.mp (hfhatc zh j c.1 (Ne.symm hc)) hnj h
        rw [hmem] at hn'; push_neg at hn'
        exact (hn' c.2).symm
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_le (Vh ∘ₗ ι)
  simp only [Module.finrank_fin_fun] at h2
  omega

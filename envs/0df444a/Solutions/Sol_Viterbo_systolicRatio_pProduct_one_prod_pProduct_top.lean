-- Prove2me | solution 1 for Viterbo.systolicRatio_pProduct_one_prod_pProduct_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T16:20:33.52299+00:00
-- url     : https://prove2.me/submissions/5e84866f-995f-42ec-8685-10c09f202d62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable

section
set_option autoImplicit false
namespace Viterbo.PProd.PartAB
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
open Viterbo
variable {n : ℕ}
/-! ## Part A: translation invariance of `cEHZ` -/
lemma pI_comm (z w : Phase n) : phaseInner z w = phaseInner w z := by
  simp [phaseInner, real_inner_comm]

lemma pI_add_left (x y w : Phase n) :
    phaseInner (x + y) w = phaseInner x w + phaseInner y w := by
  simp [phaseInner, inner_add_left]; ring

/-- `phaseInner · w` as a continuous linear functional. -/
noncomputable def pIL (w : Phase n) : Phase n →L[ℝ] ℝ :=
  (innerSL ℝ w.1).comp (ContinuousLinearMap.fst ℝ (Position n) (Position n)) +
    (innerSL ℝ w.2).comp (ContinuousLinearMap.snd ℝ (Position n) (Position n))

lemma pIL_apply (w z : Phase n) : pIL w z = phaseInner z w := by
  simp [pIL, phaseInner, real_inner_comm]

lemma J_add (x y : Phase n) : J (x + y) = J x + J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

lemma frontier_translate (S : Set (Phase n)) (w : Phase n) :
    frontier ((· + w) '' S) = (· + w) '' frontier S :=
  ((Homeomorph.addRight w).image_frontier S).symm

lemma normalCone_translate (S : Set (Phase n)) (w z : Phase n) :
    normalCone phaseInner ((· + w) '' S) (z + w) = normalCone phaseInner S z := by
  ext u
  simp only [normalCone, mem_ofPred_eq, forall_mem_image, add_sub_add_right_eq_sub]

lemma gcc_translate {S : Set (Phase n)} {γ : ℝ → Phase n}
    (h : IsGeneralizedClosedCharacteristic S γ) (w : Phase n) :
    IsGeneralizedClosedCharacteristic ((· + w) '' S) (fun t => γ t + w) := by
  obtain ⟨hper, hfr, v, hvint, hftc, hae⟩ := h
  refine ⟨fun t => by simp [hper t], fun t => ?_, v, hvint, fun a b => ?_, ?_⟩
  · rw [frontier_translate]; exact mem_image_of_mem _ (hfr t)
  · rw [← hftc a b]; exact add_sub_add_right_eq_sub _ _ _
  · filter_upwards [hae] with t ht
    rwa [normalCone_translate]

lemma action_translate {S : Set (Phase n)} {γ : ℝ → Phase n}
    (h : IsGeneralizedClosedCharacteristic S γ) (w : Phase n) :
    action (fun t => γ t + w) = action γ := by
  obtain ⟨hper, -, v, hvint, hftc, -⟩ := h
  have hvI : ∀ a b : ℝ, IntervalIntegrable v volume a b := fun a b =>
    (hvint.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hγeq : γ = fun x => γ 0 + ∫ s in (0 : ℝ)..x, v s := by
    funext x; rw [← hftc 0 x]; abel
  have hder : ∀ᵐ x, HasDerivAt γ (v x) x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hvint] with x hx
    rw [hγeq]
    simpa using (hx 0).const_add (γ 0)
  have hd : deriv (fun t => γ t + w) = deriv γ := by
    funext t; exact deriv_add_const w
  set f : ℝ → ℝ := fun t => phaseInner (J (γ t)) (deriv γ t) with hf_def
  set g : ℝ → ℝ := fun t => phaseInner (J w) (deriv γ t) with hg_def
  have hgv : g =ᵐ[volume] fun t => pIL (J w) (v t) := by
    filter_upwards [hder] with t ht
    simp only [g, ht.deriv, pIL_apply, pI_comm]
  have hvI' : IntervalIntegrable (fun t => pIL (J w) (v t)) volume 0 1 :=
    ⟨(pIL (J w)).integrable_comp (hvI 0 1).1, (pIL (J w)).integrable_comp (hvI 0 1).2⟩
  have hgI : IntervalIntegrable g volume 0 1 := by
    exact hvI'.congr_ae (ae_restrict_of_ae hgv.symm)
  have hg0 : ∫ t in (0 : ℝ)..1, g t = 0 := by
    rw [intervalIntegral.integral_congr_ae (hgv.mono fun t ht _ => ht)]
    rw [(pIL (J w)).intervalIntegral_comp_comm (hvI 0 1), ← hftc 0 1]
    have : γ 1 = γ 0 := by simpa using hper 0
    rw [this, sub_self, map_zero]
  have hsum : (fun t => phaseInner (J (γ t + w)) (deriv (fun t => γ t + w) t)) =
      fun t => f t + g t := by
    funext t; simp only [f, g, hd, J_add, pI_add_left]
  unfold action
  rw [hsum]
  by_cases hf : IntervalIntegrable f volume 0 1
  · rw [intervalIntegral.integral_add hf hgI, hg0, add_zero]
  · have : ¬ IntervalIntegrable (fun t => f t + g t) volume 0 1 := fun h =>
      hf (by simpa using h.sub hgI)
    rw [intervalIntegral.integral_undef this, intervalIntegral.integral_undef hf]

lemma cEHZ_translate_le (S : Set (Phase n)) (w : Phase n) :
    cEHZ ((· + w) '' S) ≤ cEHZ S := by
  refine le_iInf₂ (fun γ hγ => ?_)
  have hnc : ∃ s t, (fun t => γ t + w) s ≠ (fun t => γ t + w) t := by
    obtain ⟨s, t, hst⟩ := hγ.2
    exact ⟨s, t, fun h => hst (add_right_cancel h)⟩
  refine (iInf₂_le (fun t => γ t + w) ⟨gcc_translate hγ.1 w, hnc⟩).trans ?_
  rw [action_translate hγ.1 w]

end Viterbo.PProd.PartAB
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartAB
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
open Viterbo
theorem cEHZ_image_add {n : ℕ} (S : Set (Phase n)) (w : Phase n) :
    cEHZ ((· + w) '' S) = cEHZ S := by
  refine le_antisymm (cEHZ_translate_le S w) ?_
  have h := cEHZ_translate_le ((· + w) '' S) (-w)
  rwa [image_image, show (fun x : Phase n => x + w + -w) = id from funext fun x => by simp,
    image_id] at h

end Viterbo.PProd.PartAB
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
/-!
Blueprint for `Viterbo.systolicRatio_pProduct_one_prod_pProduct_top` as a reduction on the sibling
`Viterbo.cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable` (Theorem 2.2, "M3").
-/
/-! ## Part A: translation invariance of `cEHZ` -/

end Viterbo.PProd
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartAB
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
open Viterbo
variable {n : ℕ}
/-! ## Part B: the billiard characterization for every polygon (Helly) -/
lemma bddAbove_inner {T : Set (Position n)} (hT : Bornology.IsBounded T) (u : Position n) :
    BddAbove ((fun x => inner ℝ x u) '' T) := by
  obtain ⟨R, hR⟩ := hT.subset_closedBall 0
  refine ⟨R * ‖u‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact (real_inner_le_norm x u).trans (by gcongr)

lemma supportFunction_add_le {T : Set (Position n)} (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) (u v : Position n) :
    supportFunction T (u + v) ≤ supportFunction T u + supportFunction T v := by
  unfold supportFunction
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [inner_add_right]
  exact add_le_add (le_csSup (bddAbove_inner hT u) ⟨x, hx, rfl⟩)
    (le_csSup (bddAbove_inner hT v) ⟨x, hx, rfl⟩)

lemma supportFunction_translate {T : Set (Position n)} (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) (a u : Position n) :
    supportFunction ((· + -a) '' T) u = supportFunction T u - inner ℝ a u := by
  unfold supportFunction
  rw [image_image]
  have : (fun x => inner ℝ (x + -a) u) =
      (OrderIso.addRight (-inner ℝ a u)) ∘ (fun x => inner ℝ x u) := by
    funext x; simp [inner_add_left, inner_neg_left]
  rw [this, image_comp, ← OrderIso.map_csSup' _ (hne.image _) (bddAbove_inner hT u)]
  simp [sub_eq_add_neg]

lemma polygonLength_translate {T : Set (Position n)} (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) (a : Position n) {m : ℕ} (q : Fin m → Position n) :
    polygonLength ((· + -a) '' T) q = polygonLength T q := by
  unfold polygonLength
  simp only [supportFunction_translate hT hne, Finset.sum_sub_distrib]
  have : ∑ i, inner ℝ a (q (finRotate m i) - q i) = 0 := by
    simp only [inner_sub_right, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp (finRotate m) (fun i => inner ℝ a (q i)), sub_self]
  rw [this, sub_zero]

lemma polygonLength_comp_perm (T : Set (Position n)) {m : ℕ} (q : Fin m → Position n)
    (e : Equiv.Perm (Fin m)) (he : ∀ i, e (finRotate m i) = finRotate m (e i)) :
    polygonLength T (q ∘ e) = polygonLength T q := by
  unfold polygonLength
  simp only [Function.comp_apply, he]
  exact Equiv.sum_comp e (fun i => supportFunction T (q (finRotate m i) - q i))

lemma finRotate_pow_val (k r : ℕ) (x : Fin (k + 1)) :
    ((finRotate (k + 1) ^ r) x).val = (x.val + r) % (k + 1) := by
  induction r generalizing x with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ r ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, finRotate_apply, Fin.val_add, Fin.val_one',
      Nat.mod_add_mod, add_right_comm, Nat.add_mod_mod, add_assoc]

lemma rot_castSucc (k : ℕ) (i : Fin k) :
    finRotate (k + 1) i.castSucc = i.succ := by
  rw [finRotate_apply, Fin.coeSucc_eq_succ]

lemma polygonLength_castSucc_le {T : Set (Position n)} (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) {k : ℕ} (q : Fin (k + 2) → Position n) :
    polygonLength T (q ∘ Fin.castSucc) ≤ polygonLength T q := by
  unfold polygonLength
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Function.comp_apply, rot_castSucc, finRotate_last, Fin.succ_last,
    Fin.castSucc_zero, Fin.succ_castSucc]
  have htri := supportFunction_add_le hT hne (q (Fin.last (k + 1)) - q (Fin.last k).castSucc)
    (q 0 - q (Fin.last (k + 1)))
  rw [show q (Fin.last (k + 1)) - q (Fin.last k).castSucc + (q 0 - q (Fin.last (k + 1))) =
    q 0 - q (Fin.last k).castSucc by abel] at htri
  linarith

lemma mem_shift_iff (K : Set (Position n)) (x t : Position n) :
    x ∈ interior K + {t} ↔ x - t ∈ interior K := by
  rw [Set.add_singleton, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨x - t, h, sub_add_cancel x t⟩

lemma step {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) {k : ℕ} (hk : n + 1 < k + 1) (q : Fin (k + 1) → Position n)
    (hq : NotTranslatableIntoInterior K q) :
    ∃ q' : Fin k → Position n, NotTranslatableIntoInterior K q' ∧
      polygonLength T q' ≤ polygonLength T q := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  let C : Fin (k + 2) → Set (Position n) := fun j => {t | q j - t ∈ interior K}
  have hconv : ∀ j ∈ (Finset.univ : Finset (Fin (k + 2))), Convex ℝ (C j) := by
    intro j _ t1 ht1 t2 ht2 a b ha hb hab
    have := hK.2.1.interior ht1 ht2 ha hb hab
    show q j - (a • t1 + b • t2) ∈ interior K
    convert this using 1
    calc q j - (a • t1 + b • t2) = (a + b) • q j - (a • t1 + b • t2) := by rw [hab, one_smul]
      _ = a • (q j - t1) + b • (q j - t2) := by rw [add_smul, smul_sub, smul_sub]; abel
  have hempty : ¬ (⋂ j ∈ (Finset.univ : Finset (Fin (k + 2))), C j).Nonempty := by
    rintro ⟨t, ht⟩
    apply hq t
    intro j
    rw [mem_shift_iff]
    simp only [Finset.mem_univ, iInter_true, mem_iInter] at ht
    exact ht j
  have hI : ∃ I : Finset (Fin (k + 2)), I.card ≤ Module.finrank ℝ (Position n) + 1 ∧
      ¬ (⋂ i ∈ I, C i).Nonempty := by
    by_contra hcon
    push Not at hcon
    exact hempty (Convex.helly_theorem' hconv (fun I _ hc => hcon I hc))
  obtain ⟨I, hIc, hIe⟩ := hI
  rw [finrank_euclideanSpace_fin] at hIc
  obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
    by_contra h
    push Not at h
    have : I = Finset.univ := Finset.eq_univ_of_forall h
    rw [this, Finset.card_univ, Fintype.card_fin] at hIc
    omega
  let e : Equiv.Perm (Fin (k + 2)) := finRotate (k + 2) ^ (j.val + 1)
  have he_last : e (Fin.last (k + 1)) = j := by
    apply Fin.ext
    show ((finRotate (k + 1 + 1) ^ (j.val + 1)) (Fin.last (k + 1))).val = j.val
    rw [finRotate_pow_val, Fin.val_last,
      show k + 1 + (j.val + 1) = j.val + (k + 1 + 1) by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt j.isLt]
  have he : ∀ i, e (finRotate (k + 2) i) = finRotate (k + 2) (e i) := by
    intro i
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, pow_mul_comm']
  refine ⟨(q ∘ e) ∘ Fin.castSucc, ?_, ?_⟩
  · intro t ht
    apply hIe
    refine ⟨t, ?_⟩
    simp only [mem_iInter]
    intro i hi
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    have hne' : e.symm i ≠ Fin.last (k + 1) := by
      intro h
      apply hij
      rw [← he_last, ← h, Equiv.apply_symm_apply]
    obtain ⟨i', hi'⟩ := Fin.exists_castSucc_eq.2 hne'
    have := ht i'
    rw [mem_shift_iff] at this
    simp only [Function.comp_apply, hi', Equiv.apply_symm_apply] at this
    exact this
  · rw [← polygonLength_comp_perm T q e he]
    exact polygonLength_castSucc_le hT hne (q ∘ e)

lemma lower_all {K T : Set (Position n)} (hK : IsConvexDomain K) (hT : Bornology.IsBounded T)
    (hne : T.Nonempty) (L : ℝ)
    (hL : ∀ (m : ℕ) (q : Fin m → Position n), m ≤ n + 1 →
      NotTranslatableIntoInterior K q → L ≤ polygonLength T q) :
    ∀ (m : ℕ) (q : Fin m → Position n), NotTranslatableIntoInterior K q →
      L ≤ polygonLength T q := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro q hq
    by_cases hm : m ≤ n + 1
    · exact hL m q hm hq
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      obtain ⟨q', hq', hle⟩ := step hK hT hne (by omega) q hq
      exact (ih k (by omega) q' hq').trans hle

end Viterbo.PProd.PartAB
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartAB
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
open Viterbo
theorem billiard_min {n : ℕ} (hn : 1 ≤ n) (K T : Set (Position n))
    (hK : IsConvexDomain K) (hT : IsConvexDomain T) :
    ∃ L : ℝ, 0 ≤ L ∧ cEHZ (K ×ˢ T) = ENNReal.ofReal L ∧
      (∃ (m : ℕ) (q : Fin m → Position n), m ≤ n + 1 ∧ NotTranslatableIntoInterior K q ∧
        polygonLength T q = L) ∧
      (∀ (m : ℕ) (q : Fin m → Position n), NotTranslatableIntoInterior K q →
        L ≤ polygonLength T q) := by
  obtain ⟨a, ha⟩ := hT.2.2
  have hne : T.Nonempty := ⟨a, interior_subset ha⟩
  set T' : Set (Position n) := (· + -a) '' T with hT'def
  have hT'img : T' = T + {-a} := (Set.add_singleton).symm
  have h0 : (0 : Position n) ∈ interior T' := by
    have := (Homeomorph.addRight (-a)).image_interior T
    rw [hT'def]
    rw [show ((· + -a) '' T : Set (Position n)) = (Homeomorph.addRight (-a)) '' T from rfl,
      ← this]
    exact ⟨a, ha, add_neg_cancel a⟩
  have hT' : IsConvexDomain T' := by
    refine ⟨?_, ?_, ⟨0, h0⟩⟩
    · rw [hT'img]; exact hT.1.add Bornology.isBounded_singleton
    · rw [hT'img]; exact hT.2.1.add (convex_singleton _)
  obtain ⟨L, hL, ⟨γ, -, -, hγL⟩, -, -, ⟨m, q, hm, hq, hqL⟩, hbound⟩ :=
    cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable n hn K T' hK hT' h0
  have hlen : ∀ (m : ℕ) (q : Fin m → Position n), polygonLength T' q = polygonLength T q :=
    fun m q => polygonLength_translate hT.1 hne a q
  have hprod : K ×ˢ T' = (· + ((0 : Position n), -a)) '' (K ×ˢ T) := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨hx, z, hz, rfl⟩
      exact ⟨(x, z), ⟨hx, hz⟩, by simp⟩
    · rintro ⟨⟨x', z⟩, ⟨hx, hz⟩, h⟩
      simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hx, z, hz, rfl⟩
  refine ⟨L, hγL ▸ abs_nonneg _, ?_, ⟨m, q, hm, hq, (hlen m q).symm.trans hqL⟩, ?_⟩
  · rw [← cEHZ_image_add (K ×ˢ T) ((0 : Position n), -a), ← hprod, hL]
  · exact lower_all hK hT.1 hne L (fun m q hm hq => (hbound m q hm hq).trans_eq (hlen m q))

end Viterbo.PProd.PartAB
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
/-! ## Part B: the billiard characterization, for any `T` and every polygon (Helly) -/
alias billiard_min := Viterbo.PProd.PartAB.billiard_min

end Viterbo.PProd
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartC
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
variable {m k : ℕ}
theorem appendPos_castAdd (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

theorem appendPos_natAdd (x : Position m) (y : Position k) (j : Fin k) :
    appendPos x y (Fin.natAdd m j) = y j := by
  simp [appendPos]

/-- The first half of a point of `ℝ^{m+k}`. -/
noncomputable def fstPart (z : Position (m + k)) : Position m :=
  (WithLp.equiv 2 (Fin m → ℝ)).symm (fun i => z (Fin.castAdd k i))

/-- The second half of a point of `ℝ^{m+k}`. -/
noncomputable def sndPart (z : Position (m + k)) : Position k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => z (Fin.natAdd m j))

theorem appendPos_ext {z w : Position (m + k)}
    (h₁ : ∀ i : Fin m, z (Fin.castAdd k i) = w (Fin.castAdd k i))
    (h₂ : ∀ j : Fin k, z (Fin.natAdd m j) = w (Fin.natAdd m j)) : z = w := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · exact h₁
  · exact h₂

/-- `appendPos` as a continuous linear equivalence. -/
noncomputable def Aeq (m k : ℕ) : (Position m × Position k) ≃L[ℝ] Position (m + k) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun p => appendPos p.1 p.2
    invFun := fun z => (fstPart z, sndPart z)
    map_add' := by
      intro p p'
      apply appendPos_ext <;> intro i <;> simp [appendPos_castAdd, appendPos_natAdd]
    map_smul' := by
      intro c p
      apply appendPos_ext <;> intro i <;> simp [appendPos_castAdd, appendPos_natAdd]
    left_inv := by
      intro p
      ext i <;> simp [fstPart, sndPart, appendPos_castAdd, appendPos_natAdd]
    right_inv := by
      intro z
      apply appendPos_ext <;> intro i <;>
        simp [fstPart, sndPart, appendPos_castAdd, appendPos_natAdd] }

@[simp] theorem Aeq_apply (p : Position m × Position k) : Aeq m k p = appendPos p.1 p.2 := rfl

theorem appendPos_surj (z : Position (m + k)) : appendPos (fstPart z) (sndPart z) = z :=
  (Aeq m k).apply_symm_apply z

theorem appendPos_inj {x x' : Position m} {y y' : Position k}
    (h : appendPos x y = appendPos x' y') : x = x' ∧ y = y' := by
  have := (Aeq m k).injective (a₁ := (x, y)) (a₂ := (x', y')) h
  simpa using this

theorem appendPos_sub (x x' : Position m) (y y' : Position k) :
    appendPos x y - appendPos x' y' = appendPos (x - x') (y - y') := by
  have := (map_sub (Aeq m k) (x, y) (x', y')).symm
  simpa using this

theorem inner_appendPos (x x' : Position m) (y y' : Position k) :
    inner (𝕜 := ℝ) (appendPos x y) (appendPos x' y') =
      inner (𝕜 := ℝ) x x' + inner (𝕜 := ℝ) y y' := by
  simp only [PiLp.inner_apply, Fin.sum_univ_add, appendPos_castAdd, appendPos_natAdd]

theorem continuous_appendPos_left (y : Position k) :
    Continuous fun x : Position m => appendPos x y :=
  (Aeq m k).continuous.comp (continuous_id.prodMk continuous_const)

end Viterbo.PProd.PartC
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartC
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
variable {n : ℕ}
theorem bddAbove_inner {Y : Set (Position n)} (hY : Bornology.IsBounded Y) (u : Position n) :
    BddAbove ((fun x => inner (𝕜 := ℝ) x u) '' Y) := by
  obtain ⟨R, hR⟩ := hY.exists_norm_le
  refine ⟨R * ‖u‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (real_inner_le_norm x u).trans (mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg u))

theorem inner_le_supportFunction {Y : Set (Position n)} (hY : Bornology.IsBounded Y)
    {y : Position n} (hy : y ∈ Y) (u : Position n) :
    inner (𝕜 := ℝ) y u ≤ supportFunction Y u :=
  le_csSup (bddAbove_inner hY u) (mem_image_of_mem _ hy)

theorem supportFunction_smul (Y : Set (Position n)) {c : ℝ} (hc : 0 ≤ c) (u : Position n) :
    supportFunction Y (c • u) = c * supportFunction Y u := by
  unfold supportFunction
  have : (fun x => inner (𝕜 := ℝ) x (c • u)) '' Y = c • ((fun x => inner (𝕜 := ℝ) x u) '' Y) := by
    rw [← Set.image_smul, Set.image_image]
    simp [real_inner_smul_right]
  rw [this, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

theorem supportFunction_zero {Y : Set (Position n)} (hY : Y.Nonempty) :
    supportFunction Y 0 = 0 := by
  unfold supportFunction
  simp [hY.image_const]

theorem sum_rotate_sub {m : ℕ} (q : Fin m → Position n) :
    ∑ i : Fin m, (q (finRotate m i) - q i) = 0 := by
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate m) q, sub_self]

theorem polygonLength_nonneg {Y : Set (Position n)} (hY : Bornology.IsBounded Y) (hne : Y.Nonempty)
    {m : ℕ} (q : Fin m → Position n) : 0 ≤ polygonLength Y q := by
  obtain ⟨y, hy⟩ := hne
  have h : inner (𝕜 := ℝ) y (∑ i : Fin m, (q (finRotate m i) - q i)) ≤ polygonLength Y q := by
    rw [inner_sum]
    exact Finset.sum_le_sum fun i _ => inner_le_supportFunction hY hy _
  rwa [sum_rotate_sub, inner_zero_right] at h

theorem polygonLength_smul (Y : Set (Position n)) {c : ℝ} (hc : 0 ≤ c) {m : ℕ}
    (q : Fin m → Position n) : polygonLength Y (c • q) = c * polygonLength Y q := by
  unfold polygonLength
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, ← smul_sub, supportFunction_smul Y hc]

end Viterbo.PProd.PartC
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartC
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
variable {m k : ℕ}
theorem pProduct_top_eq (Y₁ : Set (Position m)) (Y₂ : Set (Position k)) :
    pProduct ⊤ Y₁ Y₂ = Aeq m k '' (Y₁ ×ˢ Y₂) := by
  ext z
  simp only [pProduct, ENNReal.inv_top, ENNReal.toReal_zero, Real.rpow_zero, one_smul,
    mem_iUnion, exists_prop]
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h; exact ⟨0, ⟨le_refl _, zero_le_one⟩, h⟩

theorem pProduct_one_eq (X₁ : Set (Position m)) (X₂ : Set (Position k)) :
    pProduct 1 X₁ X₂ = ⋃ t ∈ Icc (0 : ℝ) 1, Aeq m k '' (((1 - t) • X₁) ×ˢ (t • X₂)) := by
  simp only [pProduct, inv_one, ENNReal.toReal_one, Real.rpow_one]
  rfl

theorem smul_add_mem_smul {n : ℕ} {X : Set (Position n)} (hX : Convex ℝ X) {a b s s' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) (hs' : 0 ≤ s') {x x' : Position n}
    (hx : x ∈ s • X) (hx' : x' ∈ s' • X) : a • x + b • x' ∈ (a * s + b * s') • X := by
  rw [hX.add_smul (mul_nonneg ha hs) (mul_nonneg hb hs')]
  refine add_mem_add ?_ ?_
  · rw [mul_smul]; exact smul_mem_smul_set hx
  · rw [mul_smul]; exact smul_mem_smul_set hx'

theorem smul_subset_of_zero_mem {n : ℕ} {X : Set (Position n)} (hX : Convex ℝ X) (h0 : (0 : Position n) ∈ X)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : s • X ⊆ X := by
  rintro _ ⟨x, hx, rfl⟩
  exact hX.smul_mem_of_zero_mem h0 hx hs

theorem pProduct_one_subset {X₁ : Set (Position m)} {X₂ : Set (Position k)} (hX₁ : Convex ℝ X₁)
    (hX₂ : Convex ℝ X₂) (h₁ : 0 ∈ X₁) (h₂ : 0 ∈ X₂) :
    pProduct 1 X₁ X₂ ⊆ Aeq m k '' (X₁ ×ˢ X₂) := by
  rw [pProduct_one_eq]
  refine iUnion₂_subset fun t ht => image_mono (prod_mono ?_ ?_)
  · exact smul_subset_of_zero_mem hX₁ h₁ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · exact smul_subset_of_zero_mem hX₂ h₂ ht

theorem isOpen_Aeq_image {S : Set (Position m × Position k)} (hS : IsOpen S) :
    IsOpen (Aeq m k '' S) :=
  (Aeq m k).toHomeomorph.isOpenMap S hS

theorem isBounded_Aeq_image {S : Set (Position m × Position k)} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (Aeq m k '' S) :=
  (Aeq m k : (Position m × Position k) →L[ℝ] Position (m + k)).lipschitz.isBounded_image hS

theorem isConvexDomain_pProduct_top {m k : ℕ} (Y₁ : Set (Position m)) (Y₂ : Set (Position k))
    (hY₁ : IsConvexDomain Y₁) (hY₂ : IsConvexDomain Y₂) :
    IsConvexDomain (pProduct ⊤ Y₁ Y₂) := by
  rw [pProduct_top_eq]
  refine ⟨isBounded_Aeq_image (hY₁.1.prod hY₂.1), ?_, ?_⟩
  · exact (hY₁.2.1.prod hY₂.2.1).linear_image
      (Aeq m k : (Position m × Position k) →L[ℝ] Position (m + k)).toLinearMap
  · obtain ⟨a, ha⟩ := hY₁.2.2
    obtain ⟨b, hb⟩ := hY₂.2.2
    refine ⟨Aeq m k (a, b), interior_maximal ?_ (isOpen_Aeq_image (isOpen_interior.prod isOpen_interior))
      (mem_image_of_mem _ ⟨ha, hb⟩)⟩
    exact image_mono (prod_mono interior_subset interior_subset)

theorem isConvexDomain_pProduct_one {m k : ℕ} (X₁ : Set (Position m)) (X₂ : Set (Position k))
    (hX₁ : IsConvexDomain X₁) (hX₂ : IsConvexDomain X₂) (h₁ : 0 ∈ X₁) (h₂ : 0 ∈ X₂) :
    IsConvexDomain (pProduct 1 X₁ X₂) := by
  refine ⟨(isBounded_Aeq_image (hX₁.1.prod hX₂.1)).subset
    (pProduct_one_subset hX₁.2.1 hX₂.2.1 h₁ h₂), ?_, ?_⟩
  · rw [pProduct_one_eq]
    intro z hz z' hz' a b ha hb hab
    simp only [mem_iUnion, exists_prop] at hz hz' ⊢
    obtain ⟨t, ht, ⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := hz
    obtain ⟨t', ht', ⟨x', y'⟩, ⟨hx', hy'⟩, rfl⟩ := hz'
    refine ⟨a * t + b * t', ⟨by nlinarith [ht.1, ht'.1], by nlinarith [ht.2, ht'.2]⟩,
      a • (x, y) + b • (x', y'), ⟨?_, ?_⟩, by simp only [map_add, map_smul]⟩
    · have e : 1 - (a * t + b * t') = a * (1 - t) + b * (1 - t') := by
        linear_combination -hab
      simp only [Prod.fst_add, Prod.smul_fst, e]
      exact smul_add_mem_smul hX₁.2.1 ha hb (by linarith [ht.2]) (by linarith [ht'.2]) hx hx'
    · simp only [Prod.snd_add, Prod.smul_snd]
      exact smul_add_mem_smul hX₂.2.1 ha hb ht.1 ht'.1 hy hy'
  · obtain ⟨a, ha⟩ := hX₁.2.2
    obtain ⟨b, hb⟩ := hX₂.2.2
    have hU : IsOpen (Aeq m k '' (((1 / 2 : ℝ) • interior X₁) ×ˢ ((1 / 2 : ℝ) • interior X₂))) :=
      isOpen_Aeq_image ((isOpen_interior.smul₀ (by norm_num)).prod
        (isOpen_interior.smul₀ (by norm_num)))
    refine ⟨Aeq m k ((1 / 2 : ℝ) • a, (1 / 2 : ℝ) • b), interior_maximal ?_ hU
      (mem_image_of_mem _ ⟨smul_mem_smul_set ha, smul_mem_smul_set hb⟩)⟩
    rw [pProduct_one_eq]
    refine subset_trans ?_ (subset_biUnion_of_mem (u := fun t => Aeq m k '' (((1 - t) • X₁) ×ˢ (t • X₂)))
      (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num))
    have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    simp only [e]
    exact image_mono (prod_mono (smul_set_mono interior_subset) (smul_set_mono interior_subset))

end Viterbo.PProd.PartC
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
/-! ## Part C: the products are convex domains, and `cEHZ` of the mixed product -/

end Viterbo.PProd
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartC
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
variable {m k : ℕ}
theorem supportFunction_prod {Y₁ : Set (Position m)} {Y₂ : Set (Position k)}
    (hb₁ : Bornology.IsBounded Y₁) (hb₂ : Bornology.IsBounded Y₂) (hn₁ : Y₁.Nonempty)
    (hn₂ : Y₂.Nonempty) (u : Position m) (v : Position k) :
    supportFunction (Aeq m k '' (Y₁ ×ˢ Y₂)) (appendPos u v) =
      supportFunction Y₁ u + supportFunction Y₂ v := by
  unfold supportFunction
  have : (fun x => inner (𝕜 := ℝ) x (appendPos u v)) '' (Aeq m k '' (Y₁ ×ˢ Y₂)) =
      (fun x => inner (𝕜 := ℝ) x u) '' Y₁ + (fun x => inner (𝕜 := ℝ) x v) '' Y₂ := by
    ext r
    constructor
    · rintro ⟨_, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, (inner_appendPos x u y v).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨_, ⟨(x, y), ⟨hx, hy⟩, rfl⟩, inner_appendPos x u y v⟩
  rw [this, csSup_add (hn₁.image _) (bddAbove_inner hb₁ u) (hn₂.image _) (bddAbove_inner hb₂ v)]

theorem polygonLength_prod {Y₁ : Set (Position m)} {Y₂ : Set (Position k)}
    (hb₁ : Bornology.IsBounded Y₁) (hb₂ : Bornology.IsBounded Y₂) (hn₁ : Y₁.Nonempty)
    (hn₂ : Y₂.Nonempty) {r : ℕ} (q₁ : Fin r → Position m) (q₂ : Fin r → Position k) :
    polygonLength (Aeq m k '' (Y₁ ×ˢ Y₂)) (fun j => appendPos (q₁ j) (q₂ j)) =
      polygonLength Y₁ q₁ + polygonLength Y₂ q₂ := by
  unfold polygonLength
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [appendPos_sub, supportFunction_prod hb₁ hb₂ hn₁ hn₂]

theorem mem_add_singleton_iff {n : ℕ} {S : Set (Position n)} {x t : Position n} :
    x ∈ S + {t} ↔ x - t ∈ S := by
  rw [add_singleton]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa using hs
  · intro h
    exact ⟨x - t, h, sub_add_cancel x t⟩

theorem cEHZ_pProduct (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X₁ Y₁ : Set (Position m)) (X₂ Y₂ : Set (Position k))
    (hX₁ : IsConvexDomain X₁) (hY₁ : IsConvexDomain Y₁) (hX₂ : IsConvexDomain X₂)
    (hY₂ : IsConvexDomain Y₂) (h₀ : 0 ∈ X₁ ∧ 0 ∈ Y₁ ∧ 0 ∈ X₂ ∧ 0 ∈ Y₂)
    (hc : cEHZ (X₁ ×ˢ Y₁) = cEHZ (X₂ ×ˢ Y₂)) :
    cEHZ (pProduct 1 X₁ X₂ ×ˢ pProduct ⊤ Y₁ Y₂) = cEHZ (X₁ ×ˢ Y₁) := by
  obtain ⟨hX₁0, hY₁0, hX₂0, hY₂0⟩ := h₀
  have hmk : 1 ≤ m + k := by omega
  obtain ⟨L₁, hL₁0, hL₁, ⟨r₁, q₁, -, hq₁, hq₁L⟩, hlow₁⟩ := billiard_min hm X₁ Y₁ hX₁ hY₁
  obtain ⟨L₂, hL₂0, hL₂, -, hlow₂⟩ := billiard_min hk X₂ Y₂ hX₂ hY₂
  have hP := isConvexDomain_pProduct_one X₁ X₂ hX₁ hX₂ hX₁0 hX₂0
  have hT := isConvexDomain_pProduct_top Y₁ Y₂ hY₁ hY₂
  obtain ⟨L, hL0, hL, ⟨r, q, -, hq, hqL⟩, hlow⟩ := billiard_min hmk _ _ hP hT
  have h12 : L₁ = L₂ := by
    rw [hL₁, hL₂] at hc
    exact (ENNReal.ofReal_eq_ofReal_iff hL₁0 hL₂0).1 hc
  have hn₁ : Y₁.Nonempty := ⟨0, hY₁0⟩
  have hn₂ : Y₂.Nonempty := ⟨0, hY₂0⟩
  rw [hL, hL₁]
  congr 1
  apply le_antisymm
  · -- the polygon `q₁ × {0}`
    have key := hlow r₁ (fun j => appendPos (q₁ j) 0) ?_
    · have h0 : polygonLength Y₂ (fun _ : Fin r₁ => (0 : Position k)) = 0 := by
        simp [polygonLength, supportFunction_zero hn₂]
      rw [pProduct_top_eq, polygonLength_prod hY₁.1 hY₂.1 hn₁ hn₂, h0, add_zero, hq₁L] at key
      exact key
    · intro t ht
      apply hq₁ (fstPart t)
      intro j
      have hj := ht j
      rw [mem_add_singleton_iff] at hj ⊢
      have e : appendPos (q₁ j) 0 - t = appendPos (q₁ j - fstPart t) (-sndPart t) := by
        conv_lhs => rw [← appendPos_surj t]
        rw [appendPos_sub, zero_sub]
      rw [e] at hj
      have hU : IsOpen {x : Position m | appendPos x (-sndPart t) ∈ interior (pProduct 1 X₁ X₂)} :=
        isOpen_interior.preimage (continuous_appendPos_left _)
      refine interior_maximal ?_ hU hj
      intro x hx
      obtain ⟨⟨x', y'⟩, ⟨hx', -⟩, he⟩ :=
        pProduct_one_subset hX₁.2.1 hX₂.2.1 hX₁0 hX₂0 (interior_subset hx)
      rw [← (appendPos_inj he).1]
      exact hx'
  · by_contra hlt
    push Not at hlt
    set q₁' : Fin r → Position m := fun j => fstPart (q j) with hq₁'
    set q₂' : Fin r → Position k := fun j => sndPart (q j) with hq₂'
    have hqs : ∀ j, q j = appendPos (q₁' j) (q₂' j) := fun j => (appendPos_surj (q j)).symm
    have hsplit : L = polygonLength Y₁ q₁' + polygonLength Y₂ q₂' := by
      rw [← hqL, pProduct_top_eq, ← polygonLength_prod hY₁.1 hY₂.1 hn₁ hn₂]
      congr 1
      exact funext hqs
    set a := polygonLength Y₁ q₁' with ha
    set b := polygonLength Y₂ q₂' with hb
    have ha0 : 0 ≤ a := polygonLength_nonneg hY₁.1 hn₁ q₁'
    have hb0 : 0 ≤ b := polygonLength_nonneg hY₂.1 hn₂ q₂'
    have hc0 : 0 < L₁ := by linarith
    set lam : ℝ := (a + (L₁ - L) / 2) / L₁ with hlam_def
    have hlam : lam * L₁ = a + (L₁ - L) / 2 := by
      rw [hlam_def]; field_simp
    have hlam0 : 0 < lam := div_pos (by linarith) hc0
    have hlam1 : lam < 1 := by
      rw [hlam_def, div_lt_one hc0]; linarith
    have hmu0 : 0 < 1 - lam := by linarith
    have h1 : ¬ NotTranslatableIntoInterior X₁ (lam⁻¹ • q₁') := by
      intro hn
      have h := hlow₁ _ _ hn
      rw [polygonLength_smul _ (inv_nonneg.2 hlam0.le)] at h
      have h' := mul_le_mul_of_nonneg_left h hlam0.le
      rw [← mul_assoc, mul_inv_cancel₀ hlam0.ne', one_mul] at h'
      linarith
    have h2 : ¬ NotTranslatableIntoInterior X₂ ((1 - lam)⁻¹ • q₂') := by
      intro hn
      have h := hlow₂ _ _ hn
      rw [polygonLength_smul _ (inv_nonneg.2 hmu0.le)] at h
      have h' := mul_le_mul_of_nonneg_left h hmu0.le
      rw [← mul_assoc, mul_inv_cancel₀ hmu0.ne', one_mul, ← h12] at h'
      have : (1 - lam) * L₁ = b + (L₁ - L) / 2 := by linarith
      linarith
    obtain ⟨t₁, ht₁⟩ : ∃ t, ∀ j, (lam⁻¹ • q₁') j ∈ interior X₁ + {t} := by
      by_contra hne
      exact h1 fun t ht => hne ⟨t, ht⟩
    obtain ⟨t₂, ht₂⟩ : ∃ t, ∀ j, ((1 - lam)⁻¹ • q₂') j ∈ interior X₂ + {t} := by
      by_contra hne
      exact h2 fun t ht => hne ⟨t, ht⟩
    have hUo : IsOpen (Aeq m k '' ((lam • interior X₁) ×ˢ ((1 - lam) • interior X₂))) :=
      isOpen_Aeq_image ((isOpen_interior.smul₀ hlam0.ne').prod (isOpen_interior.smul₀ hmu0.ne'))
    have hUP : Aeq m k '' ((lam • interior X₁) ×ˢ ((1 - lam) • interior X₂)) ⊆
        pProduct 1 X₁ X₂ := by
      rw [pProduct_one_eq]
      refine subset_trans ?_ (subset_biUnion_of_mem
        (u := fun t => Aeq m k '' (((1 - t) • X₁) ×ˢ (t • X₂)))
        (show 1 - lam ∈ Icc (0 : ℝ) 1 from ⟨hmu0.le, by linarith⟩))
      simp only [sub_sub_cancel]
      exact image_mono (prod_mono (smul_set_mono interior_subset) (smul_set_mono interior_subset))
    apply hq (appendPos (lam • t₁) ((1 - lam) • t₂))
    intro j
    rw [mem_add_singleton_iff]
    refine interior_maximal hUP hUo ⟨(q₁' j - lam • t₁, q₂' j - (1 - lam) • t₂), ⟨?_, ?_⟩, ?_⟩
    · have h := ht₁ j
      rw [mem_add_singleton_iff, Pi.smul_apply] at h
      have h' := smul_mem_smul_set (a := lam) h
      rwa [smul_sub, smul_inv_smul₀ hlam0.ne'] at h'
    · have h := ht₂ j
      rw [mem_add_singleton_iff, Pi.smul_apply] at h
      have h' := smul_mem_smul_set (a := 1 - lam) h
      rwa [smul_sub, smul_inv_smul₀ hmu0.ne'] at h'
    · rw [Aeq_apply, ← appendPos_sub, hqs j]

end Viterbo.PProd.PartC
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
alias cEHZ_pProduct := Viterbo.PProd.PartC.cEHZ_pProduct

end Viterbo.PProd
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartE
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
variable {m k : ℕ}
theorem appendPos_castAdd (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

theorem appendPos_natAdd (x : Position m) (y : Position k) (j : Fin k) :
    appendPos x y (Fin.natAdd m j) = y j := by
  simp [appendPos]

/-- The first half of a point of `ℝ^{m+k}`. -/
noncomputable def fstPart (z : Position (m + k)) : Position m :=
  (WithLp.equiv 2 (Fin m → ℝ)).symm (fun i => z (Fin.castAdd k i))

/-- The second half of a point of `ℝ^{m+k}`. -/
noncomputable def sndPart (z : Position (m + k)) : Position k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => z (Fin.natAdd m j))

theorem appendPos_ext {z w : Position (m + k)}
    (h₁ : ∀ i : Fin m, z (Fin.castAdd k i) = w (Fin.castAdd k i))
    (h₂ : ∀ j : Fin k, z (Fin.natAdd m j) = w (Fin.natAdd m j)) : z = w := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · exact h₁
  · exact h₂

end Viterbo.PProd.PartE
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
/-!
# Part D1: `(m+k)! Vol(X₁ ⊗₁ X₂) = m! Vol X₁ · k! Vol X₂`

Route (the exponential-gauge trick, adapted from `Solutions/Viterbo/PP2PartV.lean`): the 1-product is
the image of `Z X₁ X₂ = ⋃ t, ((1-t) X₁) × (t X₂)` under the volume-preserving map `appendPos`. For a
measurable star-shaped `K` in a space of real dimension `n`, `∫ ρ{s | s⁻¹ x ∈ K} dx = n! Vol K` with
`ρ = e^{-s} ds` on `(0, ∞)` (Tonelli and the Gamma integral), and the integrand factorizes over
`Z X₁ X₂` (the gauge of a 1-product is the sum of the gauges). This gives the identity for compact
star-shaped sets; convex domains containing `0` are sandwiched between compact star-shaped sets of
almost the same volume.
-/
/-! ## `appendPos` is volume preserving -/
@[simp] theorem appendPos_castAdd' {m k : ℕ} (x : Position m) (y : Position k) (i : Fin m) :
    appendPos x y (Fin.castAdd k i) = x i := by
  simp [appendPos]

@[simp] theorem appendPos_natAdd' {m k : ℕ} (x : Position m) (y : Position k) (j : Fin k) :
    appendPos x y (Fin.natAdd m j) = y j := by
  simp [appendPos]

end Viterbo.PProd.PartD1
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartE
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
variable {m k : ℕ}
/-- `appendPos` as a continuous linear equivalence. -/
noncomputable def Aeq (m k : ℕ) : (Position m × Position k) ≃L[ℝ] Position (m + k) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun p => appendPos p.1 p.2
    invFun := fun z => (fstPart z, sndPart z)
    map_add' := by
      intro p p'
      apply appendPos_ext <;> intro i <;> simp [appendPos_castAdd, appendPos_natAdd]
    map_smul' := by
      intro c p
      apply appendPos_ext <;> intro i <;> simp [appendPos_castAdd, appendPos_natAdd]
    left_inv := by
      intro p
      ext i <;> simp [fstPart, sndPart, appendPos_castAdd, appendPos_natAdd]
    right_inv := by
      intro z
      apply appendPos_ext <;> intro i <;>
        simp [fstPart, sndPart, appendPos_castAdd, appendPos_natAdd] }

@[simp] theorem Aeq_apply (p : Position m × Position k) : Aeq m k p = appendPos p.1 p.2 := rfl

theorem inner_appendPos (x x' : Position m) (y y' : Position k) :
    inner (𝕜 := ℝ) (appendPos x y) (appendPos x' y') =
      inner (𝕜 := ℝ) x x' + inner (𝕜 := ℝ) y y' := by
  simp only [PiLp.inner_apply, Fin.sum_univ_add, appendPos_castAdd, appendPos_natAdd]

theorem pProduct_top_eq (Y₁ : Set (Position m)) (Y₂ : Set (Position k)) :
    pProduct ⊤ Y₁ Y₂ = Aeq m k '' (Y₁ ×ˢ Y₂) := by
  ext z
  simp only [pProduct, ENNReal.inv_top, ENNReal.toReal_zero, Real.rpow_zero, one_smul,
    mem_iUnion, exists_prop]
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h; exact ⟨0, ⟨le_refl _, zero_le_one⟩, h⟩

/-- `Aeq` precomposed with `toLp`, as a linear isometry equivalence. -/
noncomputable def AeqL (m k : ℕ) : WithLp 2 (Position m × Position k) ≃ₗᵢ[ℝ] Position (m + k) :=
  LinearEquiv.isometryOfInner
    ((WithLp.linearEquiv 2 ℝ (Position m × Position k)).trans (Aeq m k).toLinearEquiv)
    (by
      intro x y
      simp only [LinearEquiv.trans_apply, WithLp.linearEquiv_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv, Aeq_apply, inner_appendPos,
        WithLp.prod_inner_apply]
      rfl)

theorem measurePreserving_Aeq : MeasurePreserving (Aeq m k) := by
  have h := (AeqL m k).measurePreserving.comp
    (WithLp.volume_preserving_toLp (Position m) (Position k))
  convert h using 1
  funext p
  rfl

end Viterbo.PProd.PartE
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartE
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
/-! ## Part D: volume of the `∞`-product -/
theorem volume_pProduct_top {m k : ℕ} (Y₁ : Set (Position m)) (Y₂ : Set (Position k)) :
    volume (pProduct ⊤ Y₁ Y₂) = volume Y₁ * volume Y₂ := by
  rw [pProduct_top_eq]
  let e : (Position m × Position k) ≃ᵐ Position (m + k) := (Aeq m k).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e := measurePreserving_Aeq
  have himg : Aeq m k '' (Y₁ ×ˢ Y₂) = e.symm ⁻¹' (Y₁ ×ˢ Y₂) := by
    rw [← e.image_eq_preimage_symm]; rfl
  rw [himg, he.symm.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]

end Viterbo.PProd.PartE
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
/-! ## Part D: volumes -/
alias volume_pProduct_top := Viterbo.PProd.PartE.volume_pProduct_top

end Viterbo.PProd
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
theorem append_mp (m k : ℕ) :
    MeasurePreserving (fun xy : Position m × Position k => appendPos xy.1 xy.2)
      (volume.prod volume) volume := by
  have h1 := (PiLp.volume_preserving_ofLp (Fin m)).prod (PiLp.volume_preserving_ofLp (Fin k))
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin k => ℝ)
  have h3 := volume_measurePreserving_piCongrLeft (fun _ : Fin (m + k) => ℝ) finSumFinEquiv
  have h4 := PiLp.volume_preserving_toLp (Fin (m + k))
  have := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun xy : Position m × Position k => appendPos xy.1 xy.2) =
      (WithLp.toLp 2 ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv) ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm ∘ Prod.map WithLp.ofLp WithLp.ofLp) := by
    funext xy
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [appendPos_castAdd', Function.comp_apply]
      rw [← finSumFinEquiv_apply_left, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply_apply]
      rfl
    · simp only [appendPos_natAdd', Function.comp_apply]
      rw [← finSumFinEquiv_apply_right, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply_apply]
      rfl
  rw [heq]
  exact this

theorem appendPos_add' {m k : ℕ} (x x' : Position m) (y y' : Position k) :
    appendPos (x + x') (y + y') = appendPos x y + appendPos x' y' := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem appendPos_smul' {m k : ℕ} (c : ℝ) (x : Position m) (y : Position k) :
    appendPos (c • x) (c • y) = c • appendPos x y := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem appendPos_bij' {m k : ℕ} : Function.Bijective
    (fun xy : Position m × Position k => appendPos xy.1 xy.2) := by
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only at h
    have h1 : x = x' := by
      ext i
      have := congrArg (fun z : Position (m + k) => z (Fin.castAdd k i)) h
      simpa using this
    have h2 : y = y' := by
      ext j
      have := congrArg (fun z : Position (m + k) => z (Fin.natAdd m j)) h
      simpa using this
    rw [h1, h2]
  · intro z
    refine ⟨((WithLp.equiv 2 _).symm (fun i => z (Fin.castAdd k i)),
      (WithLp.equiv 2 _).symm (fun j => z (Fin.natAdd m j))), ?_⟩
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

noncomputable def appendLin (m k : ℕ) : (Position m × Position k) →ₗ[ℝ] Position (m + k) where
  toFun xy := appendPos xy.1 xy.2
  map_add' a b := appendPos_add' a.1 b.1 a.2 b.2
  map_smul' c a := appendPos_smul' c a.1 a.2

noncomputable def appendL (m k : ℕ) : (Position m × Position k) ≃L[ℝ] Position (m + k) :=
  (LinearEquiv.ofBijective (appendLin m k) appendPos_bij').toContinuousLinearEquiv

noncomputable def appendE (m k : ℕ) : (Position m × Position k) ≃ᵐ Position (m + k) :=
  (appendL m k).toHomeomorph.toMeasurableEquiv

theorem appendE_coe (m k : ℕ) : (⇑(appendE m k) : Position m × Position k → Position (m + k)) =
    fun xy => appendPos xy.1 xy.2 := rfl

theorem volume_image_append (m k : ℕ) (Z : Set (Position m × Position k)) :
    volume ((fun xy : Position m × Position k => appendPos xy.1 xy.2) '' Z) =
      (volume.prod volume) Z := by
  rw [← appendE_coe, MeasurableEquiv.image_eq_preimage_symm]
  have hmp : MeasurePreserving (appendE m k) (volume.prod volume) volume := by
    rw [appendE_coe]; exact append_mp m k
  exact (hmp.symm _).measure_preimage_equiv Z

/-! ## The exponential-gauge computation -/
noncomputable def rho : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (Real.exp (-s)))

theorem rho_apply (T : Set ℝ) :
    rho T = ∫⁻ s in T ∩ Ioi 0, ENNReal.ofReal (Real.exp (-s)) := by
  rw [rho, withDensity_apply', Measure.restrict_restrict' measurableSet_Ioi]

theorem setLIntegral_exp_Ioi {γ : ℝ} :
    ∫⁻ s in Ioi γ, ENNReal.ofReal (Real.exp (-s)) = ENNReal.ofReal (Real.exp (-γ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi γ)
    (Eventually.of_forall (fun s => (Real.exp_pos _).le)), integral_exp_neg_Ioi]

theorem rho_eq {T : Set ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (h1 : Ioi γ ⊆ T) (h2 : T ∩ Ioi 0 ⊆ Ici γ) :
    rho T = ENNReal.ofReal (Real.exp (-γ)) := by
  rw [rho_apply]
  apply le_antisymm
  · calc _ ≤ ∫⁻ s in Ici γ, ENNReal.ofReal (Real.exp (-s)) := lintegral_mono_set h2
      _ = ∫⁻ s in Ioi γ, ENNReal.ofReal (Real.exp (-s)) :=
          setLIntegral_congr Ioi_ae_eq_Ici.symm
      _ = _ := setLIntegral_exp_Ioi
  · rw [← setLIntegral_exp_Ioi]
    apply lintegral_mono_set
    intro s hs
    exact ⟨h1 hs, lt_of_le_of_lt hγ hs⟩

theorem rho_zero {T : Set ℝ} (h : T ∩ Ioi 0 = ∅) : rho T = 0 := by
  rw [rho_apply, h, Measure.restrict_empty, lintegral_zero_measure]

instance : SFinite rho := by unfold rho; infer_instance

theorem lintegral_pow_exp (n : ℕ) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (s ^ n) =
      (n.factorial : ℝ≥0∞) := by
  have hG := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at hG
  have hconv := Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at hG hconv
  rw [← ENNReal.ofReal_natCast, hG, ofReal_integral_eq_lintegral_ofReal hconv]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simp only
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (le_of_lt hs) _)

end Viterbo.PProd.PartD1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
theorem measurableSet_W {K : Set V} (hK : MeasurableSet K) :
    MeasurableSet {p : V × ℝ | p.2⁻¹ • p.1 ∈ K} := by
  have : Measurable (fun p : V × ℝ => p.2⁻¹ • p.1) :=
    measurable_snd.inv.smul measurable_fst
  exact this hK

theorem tonelli (μ : Measure V) [μ.IsAddHaarMeasure] {n : ℕ}
    (hd : Module.finrank ℝ V = n) {K : Set V} (hK : MeasurableSet K) :
    ∫⁻ x, rho {s | s⁻¹ • x ∈ K} ∂μ = (n.factorial : ℝ≥0∞) * μ K := by
  have hW := measurableSet_W hK
  have h1 : ∫⁻ x, rho {s | s⁻¹ • x ∈ K} ∂μ = (μ.prod rho) {p : V × ℝ | p.2⁻¹ • p.1 ∈ K} :=
    (Measure.prod_apply hW).symm
  rw [h1, Measure.prod_apply_symm hW, rho,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_measure_prodMk_right hW)]
  have h2 : ∀ s ∈ Ioi (0 : ℝ), ((fun s => ENNReal.ofReal (Real.exp (-s))) *
      fun y => μ ((fun x => (x, y)) ⁻¹' {p : V × ℝ | p.2⁻¹ • p.1 ∈ K})) s =
      ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (s ^ n) * μ K := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hset : ((fun x => (x, s)) ⁻¹' {p : V × ℝ | p.2⁻¹ • p.1 ∈ K}) = s • K := by
      ext x
      simp [mem_smul_set_iff_inv_smul_mem₀ hs'.ne']
    simp only [Pi.mul_apply]
    rw [hset, Measure.addHaar_smul, hd, abs_of_pos (pow_pos hs' _), mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_mul_const _ (by fun_prop),
    lintegral_pow_exp]

end Viterbo.PProd.PartD1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
open scoped Classical
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
/-- Star-shaped about `0`, containing `0`. -/
def IsStar (X : Set V) : Prop := (0 : V) ∈ X ∧ ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ x ∈ X, c • x ∈ X

/-- The scales `u > 0` with `x ∈ u • X`. -/
def Asc (X : Set V) (x : V) : Set ℝ := {u | 0 < u ∧ u⁻¹ • x ∈ X}

theorem Asc_up {X : Set V} (hX : IsStar X) {x : V} {u u' : ℝ} (hu : u ∈ Asc X x) (h : u ≤ u') :
    u' ∈ Asc X x := by
  have hu0 := hu.1
  have hu'0 : 0 < u' := lt_of_lt_of_le hu0 h
  refine ⟨hu'0, ?_⟩
  have hc1 : u / u' ≤ 1 := (div_le_one hu'0).mpr h
  have := hX.2 (u / u') (by positivity) hc1 _ hu.2
  rw [smul_smul] at this
  convert this using 2
  field_simp

theorem Asc_bdd (X : Set V) (x : V) : BddBelow (Asc X x) := ⟨0, fun _ hu => hu.1.le⟩

theorem Asc_sInf_nonneg (X : Set V) (x : V) : 0 ≤ sInf (Asc X x) :=
  Real.sInf_nonneg (fun _ hu => hu.1.le)

theorem Asc_Ioi {X : Set V} (hX : IsStar X) {x : V} (hne : (Asc X x).Nonempty) :
    Ioi (sInf (Asc X x)) ⊆ Asc X x := by
  intro s hs
  obtain ⟨u, hu, hus⟩ := exists_lt_of_csInf_lt hne hs
  exact Asc_up hX hu hus.le

theorem Asc_ge {X : Set V} {x : V} {u : ℝ} (hu : u ∈ Asc X x) : sInf (Asc X x) ≤ u :=
  csInf_le (Asc_bdd X x) hu

theorem rho_T {X : Set V} (hX : IsStar X) (x : V) :
    rho {s | s⁻¹ • x ∈ X} =
      if (Asc X x).Nonempty then ENNReal.ofReal (Real.exp (-sInf (Asc X x))) else 0 := by
  split_ifs with hne
  · apply rho_eq (Asc_sInf_nonneg X x)
    · intro s hs
      exact (Asc_Ioi hX hne hs).2
    · rintro s ⟨hs, hs0⟩
      exact Asc_ge ⟨hs0, hs⟩
  · apply rho_zero
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
    intro hs hs0
    exact hne ⟨s, hs0, hs⟩

theorem Asc_zero {X : Set V} (hX : IsStar X) : Asc X 0 = Ioi 0 := by
  ext u
  simp [Asc, smul_zero, hX.1]

theorem key_le {X : Set V} (hX : IsStar X) {a : V} {s w : ℝ} (hs : 0 < s) (hw : 0 ≤ w)
    (h : s⁻¹ • a ∈ w • X) : (Asc X a).Nonempty ∧ sInf (Asc X a) ≤ s * w := by
  rcases hw.eq_or_lt with rfl | hw
  · rw [zero_smul_set ⟨0, hX.1⟩, Set.mem_zero, smul_eq_zero] at h
    have ha : a = 0 := h.resolve_left (inv_ne_zero hs.ne')
    subst ha
    rw [Asc_zero hX, csInf_Ioi, mul_zero]
    exact ⟨⟨1, mem_Ioi.mpr one_pos⟩, le_rfl⟩
  · have hmem : s * w ∈ Asc X a := by
      refine ⟨mul_pos hs hw, ?_⟩
      rw [mem_smul_set_iff_inv_smul_mem₀ hw.ne', smul_smul] at h
      rw [mul_inv, mul_comm]
      exact h
    exact ⟨⟨_, hmem⟩, Asc_ge hmem⟩

theorem key_mem {X : Set V} {a : V} {s w : ℝ} (hw : 0 < w)
    (h : s * w ∈ Asc X a) : s⁻¹ • a ∈ w • X := by
  rw [mem_smul_set_iff_inv_smul_mem₀ hw.ne', smul_smul]
  have := h.2
  rw [mul_inv, mul_comm] at this
  exact this

end Viterbo.PProd.PartD1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
open scoped Classical
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
/-- The `1`-product as a subset of `E × F`. -/
def Z (X : Set E) (Y : Set F) : Set (E × F) :=
  ⋃ t ∈ Icc (0 : ℝ) 1, ((1 - t) • X) ×ˢ (t • Y)

theorem mem_Z_smul {X : Set E} {Y : Set F} (s : ℝ) (a : E) (b : F) :
    s⁻¹ • (a, b) ∈ Z X Y ↔
      ∃ t ∈ Icc (0 : ℝ) 1, s⁻¹ • a ∈ (1 - t) • X ∧ s⁻¹ • b ∈ t • Y := by
  simp only [Z, mem_iUnion, mem_prod, Prod.smul_mk, exists_prop]

theorem rho_Z {X : Set E} {Y : Set F} (hX : IsStar X) (hY : IsStar Y) (a : E) (b : F) :
    rho {s | s⁻¹ • (a, b) ∈ Z X Y} =
      if (Asc X a).Nonempty ∧ (Asc Y b).Nonempty then
        ENNReal.ofReal (Real.exp (-(sInf (Asc X a) + sInf (Asc Y b)))) else 0 := by
  split_ifs with hne
  · have hα := Asc_sInf_nonneg X a
    have hβ := Asc_sInf_nonneg Y b
    apply rho_eq (add_nonneg hα hβ)
    · intro s hs
      simp only [mem_Ioi] at hs
      have hs0 : 0 < s := lt_of_le_of_lt (add_nonneg hα hβ) hs
      set α := sInf (Asc X a)
      set β := sInf (Asc Y b)
      set d := (s - α - β) / 2
      have hd : 0 < d := by simp only [d]; linarith
      have hu : α + d ∈ Asc X a := Asc_Ioi hX hne.1 (by simp only [mem_Ioi]; linarith)
      have hv : β + d ∈ Asc Y b := Asc_Ioi hY hne.2 (by simp only [mem_Ioi]; linarith)
      rw [mem_ofPred_eq, mem_Z_smul]
      have huv : (α + d) + (β + d) = s := by simp only [d]; ring
      refine ⟨(β + d) / s, ⟨by positivity, (div_le_one hs0).mpr (by linarith)⟩, ?_, ?_⟩
      · have h1 : 1 - (β + d) / s = (α + d) / s := by field_simp; linarith
        rw [h1]
        apply key_mem (by positivity)
        rwa [mul_div_cancel₀ _ hs0.ne']
      · apply key_mem (by positivity)
        rwa [mul_div_cancel₀ _ hs0.ne']
    · rintro s ⟨hs, hs0⟩
      rw [mem_ofPred_eq, mem_Z_smul] at hs
      obtain ⟨t, ht, h1, h2⟩ := hs
      have k1 := (key_le hX hs0 (by linarith [ht.2]) h1).2
      have k2 := (key_le hY hs0 ht.1 h2).2
      simp only [mem_Ici]
      nlinarith
  · apply rho_zero
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
    intro hs hs0
    rw [mem_Z_smul] at hs
    obtain ⟨t, ht, h1, h2⟩ := hs
    exact hne ⟨(key_le hX hs0 (by linarith [ht.2]) h1).1, (key_le hY hs0 ht.1 h2).1⟩

theorem rho_Z_mul {X : Set E} {Y : Set F} (hX : IsStar X) (hY : IsStar Y) (p : E × F) :
    rho {s | s⁻¹ • p ∈ Z X Y} =
      rho {s | s⁻¹ • p.1 ∈ X} * rho {s | s⁻¹ • p.2 ∈ Y} := by
  obtain ⟨a, b⟩ := p
  rw [rho_Z hX hY, rho_T hX, rho_T hY]
  split_ifs with h h1 h2 <;> try simp_all
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

end Viterbo.PProd.PartD1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
theorem main_measurable (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {m k : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = k)
    {X : Set E} {Y : Set F} (hX : IsStar X) (hY : IsStar Y) (hXm : MeasurableSet X)
    (hYm : MeasurableSet Y) (hZ : MeasurableSet (Z X Y)) :
    ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Z X Y) =
      ((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y) := by
  have hd : Module.finrank ℝ (E × F) = m + k := by
    rw [Module.finrank_prod, hE, hF]
  rw [← tonelli (μ.prod ν) hd hZ, ← tonelli μ hE hXm, ← tonelli ν hF hYm]
  simp_rw [rho_Z_mul hX hY]
  exact lintegral_prod_mul (measurable_measure_prodMk_left (measurableSet_W hXm)).aemeasurable
    (measurable_measure_prodMk_left (measurableSet_W hYm)).aemeasurable

theorem Z_eq_image (X : Set E) (Y : Set F) :
    Z X Y = (fun q : ℝ × E × F => ((1 - q.1) • q.2.1, q.1 • q.2.2)) ''
      (Icc 0 1 ×ˢ (X ×ˢ Y)) := by
  ext ⟨a, b⟩
  simp only [Z, mem_iUnion, mem_prod, mem_image, exists_prop, Prod.mk.injEq, mem_smul_set,
    Prod.exists]
  constructor
  · rintro ⟨t, ht, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
    exact ⟨t, x, y, ⟨ht, hx, hy⟩, rfl, rfl⟩
  · rintro ⟨t, x, y, ⟨ht, hx, hy⟩, rfl, rfl⟩
    exact ⟨t, ht, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

theorem Z_compact {X : Set E} {Y : Set F} (hX : IsCompact X) (hY : IsCompact Y) :
    IsCompact (Z X Y) := by
  rw [Z_eq_image]
  apply (isCompact_Icc.prod (hX.prod hY)).image
  fun_prop

theorem Z_mono {X X' : Set E} {Y Y' : Set F} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    Z X Y ⊆ Z X' Y' := by
  apply iUnion₂_mono
  intro t _
  exact prod_mono (smul_set_mono hX) (smul_set_mono hY)

theorem main_compact (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {m k : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = k)
    {X : Set E} {Y : Set F} (hX : IsStar X) (hY : IsStar Y) (hXc : IsCompact X)
    (hYc : IsCompact Y) :
    ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Z X Y) =
      ((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y) :=
  main_measurable μ ν hE hF hX hY hXc.isClosed.measurableSet hYc.isClosed.measurableSet
    (Z_compact hXc hYc).isClosed.measurableSet

end Viterbo.PProd.PartD1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
theorem isStar_of_convex {X : Set E} (hX : Convex ℝ X) (h0 : (0 : E) ∈ X) : IsStar X :=
  ⟨h0, fun _ hc0 hc1 _ hx => hX.smul_mem_of_zero_mem h0 hx ⟨hc0, hc1⟩⟩

theorem measure_closure_convex (μ : Measure E) [μ.IsAddHaarMeasure] {X : Set E}
    (hX : Convex ℝ X) : μ (closure X) = μ X := by
  apply le_antisymm _ (measure_mono subset_closure)
  rw [closure_eq_self_union_frontier]
  calc μ (X ∪ frontier X) ≤ μ X + μ (frontier X) := measure_union_le _ _
    _ = μ X := by rw [hX.addHaar_frontier μ, add_zero]

/-- Inner compact star-shaped approximant. -/
def Kin (X : Set E) (c : E) (r : ℝ) : Set E :=
  (fun q : ℝ × E => q.1 • q.2) '' (Icc 0 1 ×ˢ (AffineMap.homothety c r '' closure X))

theorem Kin_compact {X : Set E} (hb : Bornology.IsBounded X) (c : E) (r : ℝ) :
    IsCompact (Kin X c r) := by
  have hcl : IsCompact (closure X) := hb.isCompact_closure
  apply (isCompact_Icc.prod (hcl.image (AffineMap.homothety_continuous c r))).image
  fun_prop

theorem Kin_star {X : Set E} {c : E} (hc : c ∈ X) (r : ℝ) : IsStar (Kin X c r) := by
  refine ⟨⟨(0, AffineMap.homothety c r c), ⟨⟨le_rfl, zero_le_one⟩,
    ⟨c, subset_closure hc, rfl⟩⟩, zero_smul _ _⟩, ?_⟩
  rintro t ht0 ht1 _ ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
  refine ⟨(t * s, y), ⟨⟨mul_nonneg ht0 hs.1, ?_⟩, hy⟩, ?_⟩
  · calc t * s ≤ 1 * 1 := mul_le_mul ht1 hs.2 hs.1 zero_le_one
      _ = 1 := one_mul 1
  · simp [smul_smul]

theorem Kin_sub {X : Set E} (hX : Convex ℝ X) (h0 : (0 : E) ∈ X) {c : E} (hc : c ∈ interior X)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Kin X c r ⊆ X := by
  rintro _ ⟨⟨s, y⟩, ⟨hs, ⟨x, hx, rfl⟩⟩, rfl⟩
  have hy : AffineMap.homothety c r x ∈ X := by
    have : AffineMap.homothety c r x = (1 - r) • c + r • x := by
      rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
      abel
    rw [this]
    exact interior_subset (hX.combo_interior_closure_mem_interior hc hx (by linarith) hr0
      (by ring))
  exact hX.smul_mem_of_zero_mem h0 hy hs

theorem Kin_vol (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ}
    (hE : Module.finrank ℝ E = m) {X : Set E} (c : E) {r : ℝ} (hr0 : 0 ≤ r) :
    ENNReal.ofReal (r ^ m) * μ X ≤ μ (Kin X c r) := by
  calc ENNReal.ofReal (r ^ m) * μ X = μ (AffineMap.homothety c r '' X) := by
        rw [Measure.addHaar_image_homothety, hE, abs_of_nonneg (pow_nonneg hr0 _)]
    _ ≤ μ (Kin X c r) := by
        apply measure_mono
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨(1, AffineMap.homothety c r x), ⟨⟨zero_le_one, le_rfl⟩,
          ⟨x, subset_closure hx, rfl⟩⟩, one_smul _ _⟩

end Viterbo.PProd.PartD1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
theorem exists_r {a : ℝ≥0∞} (ha : a < 1) (N : ℕ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ a < ENNReal.ofReal (r ^ N) := by
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ N)) (𝓝[<] 1) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ N)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ N))) :=
      (ENNReal.continuous_ofReal.comp (continuous_pow N)).tendsto 1
    rw [one_pow, ENNReal.ofReal_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨r, h1, h2⟩ := ((ht.eventually (lt_mem_nhds ha)).and
    (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))).exists
  exact ⟨r, h2.1, h2.2, h1⟩

theorem main_convex (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {m k : ℕ} (hE : Module.finrank ℝ E = m) (hF : Module.finrank ℝ F = k)
    {X : Set E} {Y : Set F} (hXb : Bornology.IsBounded X) (hYb : Bornology.IsBounded Y)
    (hXc : Convex ℝ X) (hYc : Convex ℝ Y) (hXi : (interior X).Nonempty)
    (hYi : (interior Y).Nonempty) (hX0 : (0 : E) ∈ X) (hY0 : (0 : F) ∈ Y) :
    ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Z X Y) =
      ((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y) := by
  apply le_antisymm
  · calc ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Z X Y)
        ≤ ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Z (closure X) (closure Y)) := by
          gcongr
          exact Z_mono subset_closure subset_closure
      _ = ((m.factorial : ℝ≥0∞) * μ (closure X)) * ((k.factorial : ℝ≥0∞) * ν (closure Y)) :=
          main_compact μ ν hE hF (isStar_of_convex hXc.closure (subset_closure hX0))
            (isStar_of_convex hYc.closure (subset_closure hY0)) hXb.isCompact_closure
            hYb.isCompact_closure
      _ = _ := by rw [measure_closure_convex μ hXc, measure_closure_convex ν hYc]
  · apply ENNReal.le_of_forall_lt_one_mul_le
    intro a ha
    obtain ⟨r, hr0, hr1, har⟩ := exists_r ha (m + k)
    obtain ⟨c, hc⟩ := hXi
    obtain ⟨d, hd⟩ := hYi
    have hpow : ENNReal.ofReal (r ^ (m + k)) =
        ENNReal.ofReal (r ^ m) * ENNReal.ofReal (r ^ k) := by
      rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hr0.le _)]
    calc a * (((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y))
        ≤ ENNReal.ofReal (r ^ (m + k)) *
          (((m.factorial : ℝ≥0∞) * μ X) * ((k.factorial : ℝ≥0∞) * ν Y)) := by
          gcongr
      _ = ((m.factorial : ℝ≥0∞) * (ENNReal.ofReal (r ^ m) * μ X)) *
          ((k.factorial : ℝ≥0∞) * (ENNReal.ofReal (r ^ k) * ν Y)) := by
          rw [hpow]; ring
      _ ≤ ((m.factorial : ℝ≥0∞) * μ (Kin X c r)) * ((k.factorial : ℝ≥0∞) * ν (Kin Y d r)) := by
          gcongr
          · exact Kin_vol μ hE c hr0.le
          · exact Kin_vol ν hF d hr0.le
      _ = ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Z (Kin X c r) (Kin Y d r)) :=
          (main_compact μ ν hE hF (Kin_star (interior_subset hc) r)
            (Kin_star (interior_subset hd) r) (Kin_compact hXb c r) (Kin_compact hYb d r)).symm
      _ ≤ ((m + k).factorial : ℝ≥0∞) * (μ.prod ν) (Z X Y) := by
          gcongr
          exact Z_mono (Kin_sub hXc hX0 hc hr0.le hr1) (Kin_sub hYc hY0 hd hr0.le hr1)

end Viterbo.PProd.PartD1
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Viterbo.PProd.PartD1
open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo
open scoped ENNReal Pointwise
/-! ## Assembly -/
theorem pProduct_one_eq_image {m k : ℕ} (X₁ : Set (Position m)) (X₂ : Set (Position k)) :
    pProduct 1 X₁ X₂ = (fun xy : Position m × Position k => appendPos xy.1 xy.2) '' Z X₁ X₂ := by
  rw [Z, image_iUnion₂, pProduct]
  simp only [inv_one, ENNReal.toReal_one, Real.rpow_one]

theorem volume_pProduct_one {m k : ℕ} (X₁ : Set (Position m)) (X₂ : Set (Position k))
    (hX₁ : IsConvexDomain X₁) (hX₂ : IsConvexDomain X₂) (h₁ : 0 ∈ X₁) (h₂ : 0 ∈ X₂) :
    ((m + k).factorial : ℝ≥0∞) * volume (pProduct 1 X₁ X₂) =
      (m.factorial : ℝ≥0∞) * volume X₁ * ((k.factorial : ℝ≥0∞) * volume X₂) := by
  rw [pProduct_one_eq_image, volume_image_append]
  exact main_convex volume volume (finrank_euclideanSpace_fin) (finrank_euclideanSpace_fin)
    hX₁.1 hX₂.1 hX₁.2.1 hX₂.2.1 hX₁.2.2 hX₂.2.2 h₁ h₂

end Viterbo.PProd.PartD1
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
alias volume_pProduct_one := Viterbo.PProd.PartD1.volume_pProduct_one

end Viterbo.PProd
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartE
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
/-! ## Part E: finiteness facts -/
theorem volume_ne_top {n : ℕ} {X : Set (Position n)} (hX : IsConvexDomain X) : volume X ≠ ⊤ :=
  hX.1.measure_lt_top.ne

end Viterbo.PProd.PartE
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
/-! ## Part E: finiteness facts -/
alias volume_ne_top := Viterbo.PProd.PartE.volume_ne_top

end Viterbo.PProd
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartE
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
theorem volume_ne_zero {n : ℕ} {X : Set (Position n)} (hX : IsConvexDomain X) : volume X ≠ 0 := by
  refine (lt_of_lt_of_le ?_ (measure_mono interior_subset)).ne'
  exact isOpen_interior.measure_pos volume hX.2.2

end Viterbo.PProd.PartE
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
alias volume_ne_zero := Viterbo.PProd.PartE.volume_ne_zero

theorem cEHZ_prod_ne_top {n : ℕ} (hn : 1 ≤ n) {X Y : Set (Position n)} (hX : IsConvexDomain X)
    (hY : IsConvexDomain Y) : cEHZ (X ×ˢ Y) ≠ ⊤ := by
  obtain ⟨L, -, hL, -⟩ := billiard_min hn X Y hX hY
  rw [hL]; exact ENNReal.ofReal_ne_top

end Viterbo.PProd
end

section
set_option autoImplicit false
namespace Viterbo.PProd.PartE
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
/-- The ENNReal arithmetic of the assembly. -/
theorem sys_algebra (m k : ℕ) (c P₁ T vX₁ vY₁ vX₂ vY₂ : ℝ≥0∞) (hc : c ≠ ⊤)
    (hX₁ : vX₁ ≠ 0) (hX₁' : vX₁ ≠ ⊤) (hY₁ : vY₁ ≠ 0) (hY₁' : vY₁ ≠ ⊤)
    (hX₂ : vX₂ ≠ 0) (hX₂' : vX₂ ≠ ⊤) (hY₂ : vY₂ ≠ 0) (hY₂' : vY₂ ≠ ⊤)
    (hP : ((m + k).factorial : ℝ≥0∞) * P₁ = (m.factorial : ℝ≥0∞) * vX₁ * ((k.factorial : ℝ≥0∞) * vX₂))
    (hT : T = vY₁ * vY₂) :
    c ^ (m + k) / (((m + k).factorial : ℝ≥0∞) * (P₁ * T)) =
      c ^ m / ((m.factorial : ℝ≥0∞) * (vX₁ * vY₁)) * (c ^ k / ((k.factorial : ℝ≥0∞) * (vX₂ * vY₂))) := by
  have h1 : ((m + k).factorial : ℝ≥0∞) * (P₁ * T) =
      ((m.factorial : ℝ≥0∞) * (vX₁ * vY₁)) * ((k.factorial : ℝ≥0∞) * (vX₂ * vY₂)) := by
    rw [← mul_assoc, hP, hT]; ring
  have hm0 : ((m.factorial : ℝ≥0∞) * (vX₁ * vY₁)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.factorial_ne_zero m)) (mul_ne_zero hX₁ hY₁)
  have hk0 : ((k.factorial : ℝ≥0∞) * (vX₂ * vY₂)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.factorial_ne_zero k)) (mul_ne_zero hX₂ hY₂)
  rw [h1, pow_add, ENNReal.mul_div_mul_comm (Or.inl hm0) (Or.inr hk0)]

end Viterbo.PProd.PartE
end

section
namespace Viterbo.PProd
open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise
alias sys_algebra := Viterbo.PProd.PartE.sys_algebra

theorem main (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X₁ Y₁ : Set (Position m)) (X₂ Y₂ : Set (Position k))
    (hX₁ : IsConvexDomain X₁) (hY₁ : IsConvexDomain Y₁) (hX₂ : IsConvexDomain X₂) (hY₂ : IsConvexDomain Y₂)
    (h₀ : 0 ∈ X₁ ∧ 0 ∈ Y₁ ∧ 0 ∈ X₂ ∧ 0 ∈ Y₂) (hc : cEHZ (X₁ ×ˢ Y₁) = cEHZ (X₂ ×ˢ Y₂)) :
    systolicRatio (pProduct 1 X₁ X₂ ×ˢ pProduct ⊤ Y₁ Y₂) =
      systolicRatio (X₁ ×ˢ Y₁) * systolicRatio (X₂ ×ˢ Y₂) := by
  have hC := cEHZ_pProduct m k hm hk X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂ h₀ hc
  simp only [systolicRatio]
  rw [hC, ← hc]
  simp only [Measure.volume_eq_prod, Measure.prod_prod]
  exact sys_algebra m k _ _ _ _ _ _ _ (cEHZ_prod_ne_top hm hX₁ hY₁)
    (volume_ne_zero hX₁) (volume_ne_top hX₁) (volume_ne_zero hY₁) (volume_ne_top hY₁)
    (volume_ne_zero hX₂) (volume_ne_top hX₂) (volume_ne_zero hY₂) (volume_ne_top hY₂)
    (volume_pProduct_one X₁ X₂ hX₁ hX₂ h₀.1 h₀.2.2.1) (volume_pProduct_top Y₁ Y₂)

end Viterbo.PProd
end

section
theorem solution (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (X₁ Y₁ : Set (OAI.SymmetricPolar.Position m)) (X₂ Y₂ : Set (OAI.SymmetricPolar.Position k))
    (hX₁ : Viterbo.IsConvexDomain X₁) (hY₁ : Viterbo.IsConvexDomain Y₁)
    (hX₂ : Viterbo.IsConvexDomain X₂) (hY₂ : Viterbo.IsConvexDomain Y₂)
    (h₀ : 0 ∈ X₁ ∧ 0 ∈ Y₁ ∧ 0 ∈ X₂ ∧ 0 ∈ Y₂) (hc : Viterbo.cEHZ (X₁ ×ˢ Y₁) = Viterbo.cEHZ (X₂ ×ˢ Y₂)) :
    Viterbo.systolicRatio (Viterbo.pProduct 1 X₁ X₂ ×ˢ Viterbo.pProduct ⊤ Y₁ Y₂) =
      Viterbo.systolicRatio (X₁ ×ˢ Y₁) * Viterbo.systolicRatio (X₂ ×ˢ Y₂) :=
  Viterbo.PProd.main m k hm hk X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂ h₀ hc

end

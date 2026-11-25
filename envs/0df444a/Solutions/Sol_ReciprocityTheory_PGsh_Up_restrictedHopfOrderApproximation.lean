-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.restrictedHopfOrderApproximation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:18.894446+00:00
-- url     : https://prove2.me/submissions/2e157fde-a9a7-4225-8c54-fd89632ed4cd

import Definitions.Def_ReciprocityTheory_DualLattices_RestrictedHopfOrderApproximationStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BasechangeProjectorIdempotentAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section W2c
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
private lemma reducedColumnMap_toZMod {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p]) (x : Fin r → ℤ_[p]) :
    psiW Bw (fun i => PadicInt.toZMod (x i)) = red p g (Bw *ᵥ x) := by
  funext i
  simp [psiW, red, Matrix.mulVec, dotProduct, map_sum, map_mul]
private lemma map_algebraMap_mulVec_comp {m n : Type} [Fintype n] (M : Matrix m n ℤ_[p]) (t : n → ℤ_[p]) :
    M.map (algebraMap ℤ_[p] R) *ᵥ (algebraMap ℤ_[p] R ∘ t) = algebraMap ℤ_[p] R ∘ (M *ᵥ t) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℤ_[p] R) M t i).symm
private lemma isHopfApproximable_congr (H : HodgeTateDatum p g v R O σ cp) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    {ℓ ℓ' : (Fin r → ℤ_[p]) → R} (h : ∀ x, ℓ x = ℓ' x) (hg : IsHopfApproximable H Bw ℓ) : IsHopfApproximable H Bw ℓ' := by
  obtain ⟨F, hF, h'⟩ := hg
  refine ⟨F, hF, fun x => ?_⟩
  obtain ⟨s, hs⟩ := h' x
  exact ⟨s, by rw [← h x]; exact hs⟩
private lemma isHopfApproximable_sum (H : HodgeTateDatum p g v R O σ cp) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    {ι : Type} (S : Finset ι) (c : ι → R) (ℓ : ι → (Fin r → ℤ_[p]) → R)
    (h : ∀ i ∈ S, IsHopfApproximable H Bw (ℓ i)) :
    IsHopfApproximable H Bw (fun x => ∑ i ∈ S, c i * ℓ i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, H.AA.carrier.zero_mem, fun x => ⟨0, ?_⟩⟩
    simp
  | insert a S ha ih =>
    obtain ⟨Fa, hFa, hax⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨FS, hFS, hSx⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨c a • Fa + FS, H.AA.carrier.add_mem (H.AA.carrier.smul_mem _ hFa) hFS, fun x => ?_⟩
    obtain ⟨sa, hsa⟩ := hax x
    obtain ⟨sS, hsS⟩ := hSx x
    refine ⟨c a * sa + sS, ?_⟩
    beta_reduce at hsS ⊢
    rw [Finset.sum_insert ha]
    rw [Pi.add_apply, Pi.smul_apply]
    simp only [Algebra.smul_def, map_add, map_mul] at hsa hsS ⊢
    linear_combination (algebraMap R C (c a)) * hsa + hsS
private lemma isHopfApproximable_comp_mulVec (H : HodgeTateDatum p g v R O σ cp) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (m : TT p g → R)
    (h : ∃ f ∈ H.AA.carrier, ∀ t : TT p g, ∃ r : R,
      algebraMap R C (m t) - f (red p g t) = algebraMap R C ((p : R) * r)) :
    IsHopfApproximable H Bw (fun x => m (Bw *ᵥ x)) := by
  obtain ⟨f, hf, hm⟩ := h
  exact ⟨f, hf, fun x => hm (Bw *ᵥ x)⟩
private lemma orthogonal_idempotent_action (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (w : Fin m) (s : TT p g) (i : Fin m) :
    H.ρ (e i) *ᵥ (H.ρ (e w) *ᵥ s) = if i = w then H.ρ (e w) *ᵥ s else 0 := by
  rw [Matrix.mulVec_mulVec, ← map_mul, horth]
  split_ifs with h
  · subst h
    rfl
  · rw [map_zero, Matrix.zero_mulVec]
private lemma projector_mul_idempotent_action (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (w : Fin m) (s : TT p g) :
    H.P *ᵥ (H.ρ (e w) *ᵥ s) = 0 := by
  rw [Matrix.mulVec_mulVec, H.projectors.2.2.2.1 (e w), hPT, Matrix.zero_mulVec]
private lemma basechangeProjector_idempotent_action (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hPT : ∀ i, H.ρ (e i) * H.P = 0)
    (w : Fin m) (s : TT p g) :
    btP H e *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s)) =
      H.ρL (e w) *ᵥ (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s))) := by
  have h0 : (algebraMap ℤ_[p] R ∘ (0 : Ix g → ℤ_[p])) = 0 := funext fun _ => map_zero _
  have hterm : ∀ i, (H.ρL (e i) * H.Bt * (H.ρ (e i)).map (algebraMap ℤ_[p] R)) *ᵥ
      (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s)) =
      if i = w then H.ρL (e w) *ᵥ (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s))) else 0 := by
    intro i
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp, orthogonal_idempotent_action H e horth w s i]
    split_ifs with h
    · subst h
      rfl
    · rw [h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hP : (H.PL * H.Bt * H.P.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ s)) = 0 := by
    rw [← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp, projector_mul_idempotent_action H e hPT w s, h0, Matrix.mulVec_zero]
  unfold btP
  rw [Matrix.add_mulVec, Matrix.sum_mulVec, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), hP, add_zero]
private lemma isHopfApproximable_row (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hPT : ∀ i, H.ρ (e i) * H.P = 0)
    (w : Fin m) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (hrange : LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))))
    (k : Fin g ⊕ Fin g) :
    IsHopfApproximable H Bw
      (fun x => ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) k) := by
  have hx : ∀ x, ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) =
      phiP H e *ᵥ (algebraMap ℤ_[p] R ∘ (Bw *ᵥ x)) := fun x => by
    rw [← Matrix.mulVec_mulVec, map_algebraMap_mulVec_comp]
  have hfix : ∀ x, H.ρ (e w) *ᵥ (Bw *ᵥ x) = Bw *ᵥ x := by
    intro x
    have hmem : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := hmem
    rw [← hs, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul, horth, if_pos rfl]
  rcases k with j | j
  · refine isHopfApproximable_congr H Bw (ℓ := fun x => (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ (Bw *ᵥ x))) j)
      (fun x => ?_) (isHopfApproximable_comp_mulVec H Bw (fun t => (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) j) (H.h4 j).1)
    rw [hx, phiP, Matrix.fromRows_mulVec]
    rfl
  · refine isHopfApproximable_congr H Bw
      (ℓ := fun x => ∑ l ∈ Finset.univ, H.ρL (e w) j l *
        (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ (Bw *ᵥ x)))) l)
      (fun x => ?_) (isHopfApproximable_sum H Bw Finset.univ (fun l => H.ρL (e w) j l)
        (fun l x => (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ (Bw *ᵥ x)))) l) (fun l _ => ?_))
    · rw [hx, phiP, Matrix.fromRows_mulVec, Sum.elim_inr]
      conv_rhs => rw [← hfix x]
      rw [basechangeProjector_idempotent_action H e horth hPT w (Bw *ᵥ x)]
      rfl
    · obtain ⟨f, hf, hfapprox⟩ := (H.h4 l).2
      obtain ⟨f', hf', hf'eq⟩ := H.h3 (e w) f hf
      refine isHopfApproximable_comp_mulVec H Bw (fun t => (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ (H.ρ (e w) *ᵥ t))) l)
        ⟨f', hf', fun t => ?_⟩
      obtain ⟨r0, hr0⟩ := hfapprox (H.ρ (e w) *ᵥ t)
      exact ⟨r0, by rw [hf'eq t]; exact hr0⟩
private lemma exists_leftInverse_of_range_eq {r : ℕ} (Q : Matrix (Ix g) (Ix g) ℤ_[p]) (hQ : Q * Q = Q)
    (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (hrange : LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin Q))
    (hker : LinearMap.ker (Matrix.mulVecLin Bw) = ⊥) :
    ∃ M : Matrix (Fin r) (Ix g) ℤ_[p], ∀ x, M *ᵥ (Bw *ᵥ x) = x := by
  classical
  have hinj : Function.Injective (Matrix.mulVecLin Bw) := LinearMap.ker_eq_bot.1 hker
  let eB := LinearEquiv.ofInjective (Matrix.mulVecLin Bw) hinj
  have hQmem : ∀ y, Matrix.mulVecLin Q y ∈ LinearMap.range (Matrix.mulVecLin Bw) := fun y => by
    rw [hrange]
    exact ⟨y, rfl⟩
  let q := (Matrix.mulVecLin Q).codRestrict (LinearMap.range (Matrix.mulVecLin Bw)) hQmem
  refine ⟨LinearMap.toMatrix' (eB.symm.toLinearMap ∘ₗ q), fun x => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have hQB : Q *ᵥ (Bw *ᵥ x) = Bw *ᵥ x := by
    have hmem : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin Q) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := hmem
    rw [← hs, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ]
  have hq : q (Bw *ᵥ x) = eB x := by
    apply Subtype.ext
    simp [q, eB, hQB]
  simp [hq]
private lemma exists_padicPairing_eq_coord {r : ℕ} (E : Matrix (Ix g) (Ix g) ℤ_[p]) (hE : IsUnit E.det)
    (M : Matrix (Fin r) (Ix g) ℤ_[p]) (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (hM : ∀ x, M *ᵥ (Bw *ᵥ x) = x) (i : Fin r) :
    ∃ s : TT p g, ∀ x, pair p g E s (Bw *ᵥ x) = x i := by
  refine ⟨(fun j => M i j) ᵥ* E⁻¹, fun x => ?_⟩
  unfold pair
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul E hE, Matrix.vecMul_one]
  have hx := congrFun (hM x) i
  rw [← hx]
  rfl
private lemma exists_eq_toZMod_val_add_mul (z : ℤ_[p]) : ∃ y : ℤ_[p], z = ((PadicInt.toZMod z).val : ℤ_[p]) + p * y := by
  have h0 : PadicInt.toZMod (z - ((PadicInt.toZMod z).val : ℤ_[p])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have hmem : z - ((PadicInt.toZMod z).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
    exact (RingHom.mem_ker).2 h0
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by linear_combination -hy⟩
private lemma p_eq_two_of_valuation_le (hS : HodgeTateSetting p v R O σ cp) (dj : R)
    (h1 : v (algebraMap R C cp) ≤ v (algebraMap R C dj))
    (h2 : v (algebraMap R C dj) ≤ v (algebraMap R C (p : R))) : p = 2 := by
  by_contra hp2
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hcv := hS.cp_val
  have hpne := hS.p_ne
  have hplt := hS.p_lt
  generalize v (algebraMap R C cp) = c at hcv h1
  have hc0 : c ≠ 0 := by
    intro hc
    apply hpne
    rw [← hcv, hc, zero_pow (by omega)]
  have hc1 : c < 1 := by
    by_contra hc
    push Not at hc
    have h1c : 1 ≤ c ^ (p - 1) := one_le_pow₀ hc
    rw [hcv] at h1c
    exact absurd hplt (not_lt.2 h1c)
  have hle : c ≤ c ^ (p - 1) := by
    rw [hcv]
    exact h1.trans h2
  have hlt : c ^ (p - 1) < c := by
    calc c ^ (p - 1) ≤ c ^ 2 := pow_le_pow_of_le_one zero_le hc1.le (by omega)
      _ < c := by
        rw [sq]
        exact mul_lt_of_lt_one_left (pos_iff_ne_zero.2 hc0) hc1
  exact absurd hle (not_le.2 hlt)
end W2c
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : RestrictedHopfOrderApproximationStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π horth hσ hsum hPT hsumL hPTL w hw r Bw hrange hker
    lam dj hspan hdj
  have hint := hS.integers
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hspan
  have hci : ∀ i, ∑ k, c k * (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i = dj * lam i := by
    intro i
    have hcf := congrFun hc i
    simpa [Finset.sum_apply, smul_eq_mul] using hcf
  have hp0 : algebraMap R C (p : R) ≠ 0 := fun h0 => hS.p_ne (by rw [h0, map_zero])
  have hcp0 : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    apply hS.p_ne
    rw [← hS.cp_val, h0, zero_pow (by have := (Fact.out : p.Prime).two_le; omega)]
  have hdj0 : 0 < v (algebraMap R C dj) := lt_of_lt_of_le (pos_iff_ne_zero.2 hcp0) hdj
  by_cases hcase : v (algebraMap R C dj) ≤ v (algebraMap R C (p : R))
  · have hp2 : p = 2 := p_eq_two_of_valuation_le hS dj hdj hcase
    have hpc : v (algebraMap R C (p : R)) = v (algebraMap R C cp) := by
      rw [← hS.cp_val, hp2]
      norm_num
    have hvdj : v (algebraMap R C dj) = v (algebraMap R C (p : R)) :=
      le_antisymm hcase (by rw [hpc]; exact hdj)
    have hQ : H.ρ (e w) * H.ρ (e w) = H.ρ (e w) := by rw [← map_mul, horth, if_pos rfl]
    obtain ⟨M, hM⟩ := exists_leftInverse_of_range_eq (H.ρ (e w)) hQ Bw hrange hker
    choose sv hsv using fun i => exists_padicPairing_eq_coord H.E H.isUnit_det_E M Bw hM i
    choose χ hχ hχv using fun i => H.h5 hp2 (sv i)
    obtain ⟨u, hu⟩ := hint.exists_of_le_one (r := algebraMap R C dj / algebraMap R C (p : R))
      (le_of_eq (by rw [Valuation.map_div, hvdj, div_self hS.p_ne]))
    have h2C : algebraMap R C (p : R) = 2 := by
      rw [map_natCast, hp2]
      norm_num
    have hu2 : algebraMap R C u * 2 = algebraMap R C dj := by rw [hu, ← h2C, div_mul_cancel₀ _ hp0]
    let F : Nb p g → C := ∑ i, (u * lam i) • ((1 : Nb p g → C) - χ i)
    have hF : F ∈ H.AA.carrier := Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.sub_mem _ H.AA.one_mem (hχ i))
    refine ⟨LinearMap.funLeft R C (psiW Bw) F, Submodule.mem_map_of_mem hF, fun x => ?_⟩
    show v (F (psiW Bw (fun i => PadicInt.toZMod (x i))) - _) < _
    rw [reducedColumnMap_toZMod]
    choose y hy using fun i => exists_eq_toZMod_val_add_mul (x i)
    have hFval : F (red p g (Bw *ᵥ x)) =
        ∑ i, algebraMap R C (dj * lam i * ((PadicInt.toZMod (x i)).val : R)) := by
      simp only [F, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, hχv, hsv]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hlt := ZMod.val_lt (PadicInt.toZMod (x i))
      rcases (show (PadicInt.toZMod (x i)).val = 0 ∨ (PadicInt.toZMod (x i)).val = 1 by omega) with h | h
      · rw [h]
        simp
      · rw [h, Algebra.smul_def]
        simp only [pow_one, Nat.cast_one, mul_one, map_mul]
        rw [← hu2]
        ring
    have hxR : ∀ i, algebraMap ℤ_[p] R (x i) =
        ((PadicInt.toZMod (x i)).val : R) + (p : R) * algebraMap ℤ_[p] R (y i) := by
      intro i
      conv_lhs => rw [hy i]
      simp only [map_add, map_mul, map_natCast]
    have hR : ∑ i, dj * lam i * ((PadicInt.toZMod (x i)).val : R) -
        dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i) =
        -(dj * (p : R) * ∑ i, lam i * algebraMap ℤ_[p] R (y i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hxR i]
      ring
    rw [hFval, ← map_sum, ← map_sub, hR, map_neg, Valuation.map_neg]
    simp only [map_mul]
    calc v (algebraMap R C dj) * v (algebraMap R C (p : R)) *
          v (algebraMap R C (∑ i, lam i * algebraMap ℤ_[p] R (y i)))
        ≤ v (algebraMap R C dj) * v (algebraMap R C (p : R)) * 1 :=
          mul_le_mul_of_nonneg_left (hint.map_le_one _) zero_le
      _ = v (algebraMap R C dj) * v (algebraMap R C (p : R)) := mul_one _
      _ < v (algebraMap R C dj) * 1 := mul_lt_mul_of_pos_left hS.p_lt hdj0
      _ = v (algebraMap R C dj) := mul_one _
  · push Not at hcase
    obtain ⟨F, hF, hFx⟩ := isHopfApproximable_sum H Bw Finset.univ c
      (fun k x => ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) k)
      (fun k _ => isHopfApproximable_row H e horth hPT w Bw hrange k)
    refine ⟨LinearMap.funLeft R C (psiW Bw) F, Submodule.mem_map_of_mem hF, fun x => ?_⟩
    obtain ⟨s, hs⟩ := hFx x
    have hlin : ∑ k, c k * ((phiP H e * Bw.map (algebraMap ℤ_[p] R)) *ᵥ (algebraMap ℤ_[p] R ∘ x)) k =
        dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i) := by
      simp only [Matrix.mulVec, dotProduct, Function.comp_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← hci i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hs' : F (red p g (Bw *ᵥ x)) - algebraMap R C (dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i)) =
        -algebraMap R C ((p : R) * s) := by
      rw [← hlin, ← hs]
      ring
    show v (F (psiW Bw (fun i => PadicInt.toZMod (x i))) - _) < _
    rw [reducedColumnMap_toZMod, hs', Valuation.map_neg, map_mul, Valuation.map_mul]
    calc v (algebraMap R C (p : R)) * v (algebraMap R C s)
        ≤ v (algebraMap R C (p : R)) * 1 := mul_le_mul_of_nonneg_left (hint.map_le_one s) zero_le
      _ = v (algebraMap R C (p : R)) := mul_one _
      _ < v (algebraMap R C dj) := hcase
end ReciprocityTheory.PGsh.Up

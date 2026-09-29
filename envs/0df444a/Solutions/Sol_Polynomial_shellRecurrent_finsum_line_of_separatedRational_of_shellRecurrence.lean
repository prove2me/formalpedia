-- Prove2me | solution 1 for Polynomial.shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6184a85b-0ecb-5a47-a99d-3025bf62b348

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence

set_option autoImplicit false

open scoped BigOperators

namespace ShellRec

def sh (k : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f := fun n => f (n + k)
  map_add' f g := by funext n; rfl
  map_smul' c f := by funext n; rfl

@[scoped simp] theorem sh_apply (k : ℕ) (f : ℕ → ℂ) (n : ℕ) : sh k f n = f (n + k) := rfl

theorem sh_zero (f : ℕ → ℂ) : sh 0 f = f := by funext n; simp
theorem sh_sh (j k : ℕ) (f : ℕ → ℂ) : sh j (sh k f) = sh (k + j) f := by funext n; simp [add_assoc, add_comm j k]
theorem sh_one_sh (k : ℕ) (f : ℕ → ℂ) : sh 1 (sh k f) = sh (k + 1) f := sh_sh 1 k f

def ShiftFinite (s : ℕ → ℂ) : Prop :=
  ∃ W : Submodule ℂ (ℕ → ℂ), FiniteDimensional ℂ W ∧ (∀ f ∈ W, sh 1 f ∈ W) ∧ ∃ K : ℕ, ∀ k, K ≤ k → sh k s ∈ W

theorem sh_mem_of_stable {W : Submodule ℂ (ℕ → ℂ)} (hW : ∀ f ∈ W, sh 1 f ∈ W) {f : ℕ → ℂ} (hf : f ∈ W) (j : ℕ) :
    sh j f ∈ W := by
  induction j with
  | zero => rwa [sh_zero]
  | succ j ih => rw [← sh_one_sh]; exact hW _ ih

def SR (x : ℤ → ℂ) : Prop :=
  ∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧ (∀ m : ℤ, m < N → x m = 0) ∧
    (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * x (N + (m : ℤ) - (i : ℤ)) = 0)

def seqAt (x : ℤ → ℂ) (N : ℤ) : ℕ → ℂ := fun m => x (N + m)

@[scoped simp] theorem seqAt_apply (x : ℤ → ℂ) (N : ℤ) (m : ℕ) : seqAt x N m = x (N + m) := rfl

theorem shiftFinite_of_rec (x : ℤ → ℂ) (N : ℤ) (E : Polynomial ℂ) (M : ℕ) (hE : E.eval 0 ≠ 0)
    (hrec : ∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * x (N + (m : ℤ) - (i : ℤ)) = 0) :
    ShiftFinite (seqAt x N) := by
  classical
  set s := seqAt x N with hs
  set d := E.natDegree with hd
  set M₁ := max M d with hM₁
  have hE0 : E.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]

  have key : ∀ k, M₁ ≤ k →
      sh k s = -((E.coeff 0)⁻¹ • ∑ i ∈ Finset.Ico 1 (d + 1), E.coeff i • sh (k - i) s) := by
    intro k hk
    have hkM : M ≤ k := le_trans (le_max_left _ _) hk
    have hkd : d ≤ k := le_trans (le_max_right _ _) hk
    funext n
    have h := hrec (k + n) (le_trans hkM (Nat.le_add_right _ _))
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)] at h
    simp only [Pi.neg_apply, Pi.smul_apply, Finset.sum_apply, sh_apply, smul_eq_mul]
    have e0 : x (N + ((k + n : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) = s (n + k) := by
      simp only [hs, seqAt_apply, Nat.cast_zero, sub_zero, Nat.cast_add]; ring_nf
    have ei : ∀ i ∈ Finset.Ico 1 (d + 1), E.coeff i * x (N + ((k + n : ℕ) : ℤ) - (i : ℤ)) = E.coeff i * s (n + (k - i)) := by
      intro i hi
      have hi' : i ≤ k := le_trans (Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hi).2) hkd
      congr 1
      simp only [hs, seqAt_apply]; congr 1; push_cast; omega
    rw [e0, Finset.sum_congr rfl ei] at h
    rw [← mul_right_inj' hE0, mul_neg, ← mul_assoc, mul_inv_cancel₀ hE0, one_mul]
    linear_combination h

  let K := M₁ - d
  let W : Submodule ℂ (ℕ → ℂ) := Submodule.span ℂ ((fun j : Fin d => sh (K + j) s) '' Set.univ)
  have hmemW : ∀ j, j < d → sh (K + j) s ∈ W := fun j hj =>
    Submodule.subset_span ⟨⟨j, hj⟩, Set.mem_univ _, rfl⟩

  have hall : ∀ k, K ≤ k → sh k s ∈ W := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hlt : k < K + d
      · obtain ⟨j, rfl⟩ : ∃ j, k = K + j := ⟨k - K, by omega⟩
        exact hmemW j (by omega)
      · rw [key k (by omega)]
        refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => ?_))
        have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
        have hi2 : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hi).2
        exact Submodule.smul_mem _ _ (ih (k - i) (by omega) (by omega))
  refine ⟨W, ?_, ?_, K, hall⟩
  · exact FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  · intro f hf
    refine Submodule.span_induction (fun g hg => ?_) (by rw [map_zero]; exact W.zero_mem)
      (fun a b _ _ ha hb => by rw [map_add]; exact W.add_mem ha hb)
      (fun c a _ ha => by rw [map_smul]; exact W.smul_mem c ha) hf
    obtain ⟨⟨j, hj⟩, -, rfl⟩ := hg
    rw [sh_one_sh]
    exact hall _ (by simp only; omega)

theorem sr_of_shiftFinite (x : ℤ → ℂ) (N : ℤ) (hN : ∀ m : ℤ, m < N → x m = 0) (hsf : ShiftFinite (seqAt x N)) :
    SR x := by
  classical
  obtain ⟨W, hfd, hW, K, hK⟩ := hsf
  haveI := hfd

  let T : W →ₗ[ℂ] W := (sh 1).restrict (fun f hf => hW f hf)
  have hTpow : ∀ (j : ℕ) (w : W), ((T ^ j) w : ℕ → ℂ) = sh j (w : ℕ → ℂ) := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, Module.End.one_apply, sh_zero]
    | succ j ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, show ((T w : W) : ℕ → ℂ) = sh 1 (w : ℕ → ℂ) from rfl, sh_sh, add_comm]
  let p := T.charpoly
  have hp : Polynomial.aeval T p = 0 := LinearMap.aeval_self_charpoly T
  set r := p.natDegree with hr
  have hmonic : p.Monic := LinearMap.charpoly_monic T

  let E := p.reverse
  have hE0 : E.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse, hmonic.leadingCoeff]; exact one_ne_zero
  refine ⟨N, E, K + r, hE0, hN, fun m hm => ?_⟩

  have hdeg : E.natDegree ≤ r := by rw [hr]; exact Polynomial.reverse_natDegree_le p
  have hsum : ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * x (N + (m : ℤ) - (i : ℤ)) =
      ∑ i ∈ Finset.range (r + 1), E.coeff i * x (N + (m : ℤ) - (i : ℤ)) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hi'
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, zero_mul]
    simp only [Finset.mem_range, not_lt] at hi hi'; omega
  rw [hsum]

  obtain ⟨k, rfl⟩ : ∃ k, m = k + r := ⟨m - r, by omega⟩
  have hk : K ≤ k := by omega
  have e1 : ∀ i ∈ Finset.range (r + 1), E.coeff i * x (N + ((k + r : ℕ) : ℤ) - (i : ℤ)) =
      p.coeff (r - i) * seqAt x N (k + (r - i)) := by
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [Polynomial.coeff_reverse, Polynomial.revAt_le (by rw [← hr]; exact hi'), seqAt_apply]
    congr 2; push_cast; omega
  rw [Finset.sum_congr rfl e1]
  have hrefl := Finset.sum_range_reflect (fun j => p.coeff j * seqAt x N (k + j)) (r + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  rw [hrefl]

  have hw : sh k (seqAt x N) ∈ W := hK k hk
  have h0 := congrArg (fun (w : W) => (w : ℕ → ℂ) 0) (show Polynomial.aeval T p ⟨_, hw⟩ = 0 by rw [hp, LinearMap.zero_apply])
  simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_zero,
    Pi.zero_apply, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, hTpow, sh_apply,
    smul_eq_mul, zero_add, ← hr] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sh_apply, seqAt_apply]; ring_nf

end ShellRec
p2m_reactivate "P2MW.S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.ShellRec"

noncomputable section

namespace ShellRec

theorem shiftFinite_of_eventually {s s' : ℕ → ℂ} (hs : ShiftFinite s) (a b K₀ : ℕ)
    (h : ∀ k, K₀ ≤ k → sh (k + a) s' = sh (k + b) s) : ShiftFinite s' := by
  obtain ⟨W, hfd, hW, K, hK⟩ := hs
  refine ⟨W, hfd, hW, K₀ + K + a, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + a := ⟨k - a, by omega⟩
  rw [h j (by omega)]
  exact hK _ (by omega)

theorem shiftFinite_add {s r : ℕ → ℂ} (hs : ShiftFinite s) (hr : ShiftFinite r) : ShiftFinite (s + r) := by
  obtain ⟨W₁, hfd₁, hW₁, K₁, hK₁⟩ := hs
  obtain ⟨W₂, hfd₂, hW₂, K₂, hK₂⟩ := hr
  haveI := hfd₁; haveI := hfd₂
  refine ⟨W₁ ⊔ W₂, Submodule.finiteDimensional_sup W₁ W₂, ?_, max K₁ K₂, fun k hk => ?_⟩
  · intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add]; exact Submodule.add_mem_sup (hW₁ _ h₁) (hW₂ _ h₂)
  · rw [map_add]
    exact Submodule.add_mem_sup (hK₁ k (le_trans (le_max_left _ _) hk)) (hK₂ k (le_trans (le_max_right _ _) hk))

theorem sh_mul (k : ℕ) (f g : ℕ → ℂ) : sh k (f * g) = sh k f * sh k g := by funext n; rfl

theorem shiftFinite_mul {s r : ℕ → ℂ} (hs : ShiftFinite s) (hr : ShiftFinite r) : ShiftFinite (s * r) := by
  obtain ⟨W₁, hfd₁, hW₁, K₁, hK₁⟩ := hs
  obtain ⟨W₂, hfd₂, hW₂, K₂, hK₂⟩ := hr
  haveI := hfd₁; haveI := hfd₂
  let μ : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := LinearMap.mul ℂ (ℕ → ℂ)
  have hμ : ∀ f g : ℕ → ℂ, μ f g = f * g := fun f g => rfl
  let W := Submodule.map₂ μ W₁ W₂
  have hfg : W.FG := Submodule.FG.map₂ μ (Module.Finite.iff_fg.1 inferInstance) (Module.Finite.iff_fg.1 inferInstance)
  refine ⟨W, Module.Finite.iff_fg.2 hfg, ?_, max K₁ K₂, fun k hk => ?_⟩
  · intro f hf
    have hle : W ≤ (W.comap (sh 1)) := by
      refine Submodule.map₂_le.2 fun f hf g hg => ?_
      rw [Submodule.mem_comap, hμ, sh_mul]
      exact Submodule.apply_mem_map₂ μ (hW₁ f hf) (hW₂ g hg)
    exact hle hf
  · rw [sh_mul, ← hμ]
    exact Submodule.apply_mem_map₂ μ (hK₁ k (le_trans (le_max_left _ _) hk)) (hK₂ k (le_trans (le_max_right _ _) hk))

def dil (e r : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f := fun i => if e ∣ i + r then f ((i + r) / e) else 0
  map_add' f g := by funext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

@[scoped simp] theorem dil_apply (e r : ℕ) (f : ℕ → ℂ) (i : ℕ) :
    dil e r f i = if e ∣ i + r then f ((i + r) / e) else 0 := rfl

theorem sh_one_dil (e r : ℕ) (f : ℕ → ℂ) : sh 1 (dil e r f) = dil e (r + 1) f := by
  funext i; simp only [sh_apply, dil_apply]; rw [show i + 1 + r = i + (r + 1) by omega]

theorem dil_add_mul (e r q : ℕ) (he : 0 < e) (f : ℕ → ℂ) : dil e (r + e * q) f = dil e r (sh q f) := by
  funext i
  simp only [dil_apply, sh_apply]
  rw [show i + (r + e * q) = i + r + e * q by omega]
  have hdvd : (e ∣ i + r + e * q) ↔ (e ∣ i + r) := by
    constructor
    · intro h; exact (Nat.dvd_add_left (Dvd.intro q rfl)).1 h
    · intro h; exact (Nat.dvd_add_left (Dvd.intro q rfl)).2 h
  by_cases h : e ∣ i + r
  · rw [if_pos (hdvd.2 h), if_pos h, Nat.add_mul_div_left _ _ he]
  · rw [if_neg (fun h' => h (hdvd.1 h')), if_neg h]

theorem sh_dil_zero (e k : ℕ) (he : 0 < e) (f : ℕ → ℂ) : sh k (dil e 0 f) = dil e (k % e) (sh (k / e) f) := by
  have : sh k (dil e 0 f) = dil e k f := by funext i; simp only [sh_apply, dil_apply, add_zero]
  rw [this]
  have h2 := dil_add_mul e (k % e) (k / e) he f
  rwa [Nat.mod_add_div] at h2

theorem shiftFinite_dil {s : ℕ → ℂ} (hs : ShiftFinite s) (e : ℕ) (he : 0 < e) : ShiftFinite (dil e 0 s) := by
  classical
  obtain ⟨W, hfd, hW, K, hK⟩ := hs
  haveI := hfd
  let W' : Submodule ℂ (ℕ → ℂ) := ⨆ r : Fin e, W.map (dil e r)
  refine ⟨W', Submodule.finiteDimensional_iSup _, ?_, e * K, fun k hk => ?_⟩
  · intro f hf
    refine Submodule.iSup_induction _ (motive := fun f => sh 1 f ∈ W') hf ?_ (by simp only [map_zero]; exact W'.zero_mem)
      (fun a b ha hb => by simp only [map_add] at ha hb ⊢; exact W'.add_mem ha hb)
    rintro ⟨r, hr⟩ f hf
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hf
    rw [sh_one_dil]
    by_cases hre : r + 1 < e
    · exact Submodule.mem_iSup_of_mem ⟨r + 1, hre⟩ (Submodule.mem_map_of_mem hg)
    · have hr1 : r + 1 = 0 + e * 1 := by omega
      rw [hr1, dil_add_mul e 0 1 he]
      exact Submodule.mem_iSup_of_mem ⟨0, he⟩ (Submodule.mem_map_of_mem (hW g hg))
  · rw [sh_dil_zero e k he]
    refine Submodule.mem_iSup_of_mem ⟨k % e, Nat.mod_lt _ he⟩ (Submodule.mem_map_of_mem (hK _ ?_))
    exact (Nat.le_div_iff_mul_le he).2 (by rw [mul_comm]; exact hk)

def convR (v : ℕ → ℂ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f := fun m => ∑ i ∈ Finset.range (m + 1), f i * v (m - i)
  map_add' f g := by funext m; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by funext m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

@[scoped simp] theorem convR_apply (v f : ℕ → ℂ) (m : ℕ) : convR v f m = ∑ i ∈ Finset.range (m + 1), f i * v (m - i) := rfl

theorem sh_one_convR (v f : ℕ → ℂ) : sh 1 (convR v f) = f 0 • sh 1 v + convR v (sh 1 f) := by
  funext m
  simp only [sh_apply, convR_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_range_succ', add_comm]
  simp only [Nat.sub_zero, Nat.add_sub_add_right, zero_add]

theorem shiftFinite_convR {u v : ℕ → ℂ} (hu : ShiftFinite u) (hv : ShiftFinite v) : ShiftFinite (convR v u) := by
  classical
  obtain ⟨Wu, hfdu, hWu, Ku, hKu⟩ := hu
  obtain ⟨Wv, hfdv, hWv, Kv, hKv⟩ := hv
  haveI := hfdu; haveI := hfdv

  let V : Submodule ℂ (ℕ → ℂ) := Submodule.span ℂ ((fun l : Fin (Kv + 1) => sh l v) '' Set.univ) ⊔ Wv
  have hVsh : ∀ l, sh l v ∈ V := by
    intro l
    by_cases hl : l < Kv + 1
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨⟨l, hl⟩, Set.mem_univ _, rfl⟩)
    · exact Submodule.mem_sup_right (hKv l (by omega))
  have hVst : ∀ f ∈ V, sh 1 f ∈ V := by
    intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add]
    refine V.add_mem ?_ (Submodule.mem_sup_right (hWv _ h₂))
    refine Submodule.span_induction (fun g hg => ?_) (by rw [map_zero]; exact V.zero_mem)
      (fun a b _ _ ha hb => by rw [map_add]; exact V.add_mem ha hb)
      (fun c a _ ha => by rw [map_smul]; exact V.smul_mem c ha) h₁
    obtain ⟨⟨l, hl⟩, -, rfl⟩ := hg
    rw [sh_one_sh]; exact hVsh _
  have hVfd : FiniteDimensional ℂ V := by
    haveI : FiniteDimensional ℂ (Submodule.span ℂ ((fun l : Fin (Kv + 1) => sh l v) '' Set.univ)) :=
      FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
    exact Submodule.finiteDimensional_sup _ _
  let W : Submodule ℂ (ℕ → ℂ) := Wu.map (convR v) ⊔ V

  have hdiff : ∀ k, sh k (convR v u) - convR v (sh k u) ∈ V := by
    intro k
    induction k with
    | zero => rw [sh_zero, sh_zero, sub_self]; exact V.zero_mem
    | succ k ih =>
      have e : sh (k + 1) (convR v u) - convR v (sh (k + 1) u) =
          sh 1 (sh k (convR v u) - convR v (sh k u)) + (sh k u) 0 • sh 1 v := by
        rw [map_sub, sh_one_sh, sh_one_convR, sh_one_sh]; abel
      rw [e]
      exact V.add_mem (hVst _ ih) (V.smul_mem _ (hVsh 1))
  refine ⟨W, ?_, ?_, Ku, fun k hk => ?_⟩
  · haveI := hVfd; exact Submodule.finiteDimensional_sup _ _
  · intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := Submodule.mem_sup.1 hf
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 h₁
    rw [map_add, sh_one_convR]
    refine W.add_mem (W.add_mem (Submodule.mem_sup_right (V.smul_mem _ (hVsh 1)))
      (Submodule.mem_sup_left (Submodule.mem_map_of_mem (hWu g hg)))) (Submodule.mem_sup_right (hVst _ h₂))
  · have := hdiff k
    rw [show sh k (convR v u) = (sh k (convR v u) - convR v (sh k u)) + convR v (sh k u) by abel]
    exact W.add_mem (Submodule.mem_sup_right this) (Submodule.mem_sup_left (Submodule.mem_map_of_mem (hKu k hk)))

end ShellRec
p2m_reactivate "P2MW.S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.ShellRec"

end
p2m_reactivate "P2MW.S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.ShellRec"

noncomputable section

namespace ShellRec

theorem shiftFinite_seqAt_of_le (x : ℤ → ℂ) {N₁ N : ℤ} (hle : N ≤ N₁) (h : ShiftFinite (seqAt x N₁)) :
    ShiftFinite (seqAt x N) := by
  refine shiftFinite_of_eventually h (N₁ - N).toNat 0 0 (fun k _ => ?_)
  funext n
  simp only [sh_apply, seqAt_apply, add_zero]
  congr 1
  have := Int.toNat_of_nonneg (sub_nonneg.2 hle)
  push_cast; omega

theorem sr_data {x : ℤ → ℂ} (hx : SR x) :
    ∃ N : ℤ, (∀ m : ℤ, m < N → x m = 0) ∧ ∀ N', N' ≤ N → ShiftFinite (seqAt x N') := by
  obtain ⟨N, E, M, hE, hz, hr⟩ := hx
  exact ⟨N, hz, fun N' hN' => shiftFinite_seqAt_of_le x hN' (shiftFinite_of_rec x N E M hE hr)⟩

theorem sr_add {x y : ℤ → ℂ} (hx : SR x) (hy : SR y) : SR (x + y) := by
  obtain ⟨N₁, hz₁, hs₁⟩ := sr_data hx
  obtain ⟨N₂, hz₂, hs₂⟩ := sr_data hy
  refine sr_of_shiftFinite (x + y) (min N₁ N₂) (fun m hm => ?_) ?_
  · rw [Pi.add_apply, hz₁ m (lt_of_lt_of_le hm (min_le_left _ _)), hz₂ m (lt_of_lt_of_le hm (min_le_right _ _)), add_zero]
  · have : seqAt (x + y) (min N₁ N₂) = seqAt x (min N₁ N₂) + seqAt y (min N₁ N₂) := by funext m; rfl
    rw [this]; exact shiftFinite_add (hs₁ _ (min_le_left _ _)) (hs₂ _ (min_le_right _ _))

theorem sr_mul {x y : ℤ → ℂ} (hx : SR x) (hy : SR y) : SR (x * y) := by
  obtain ⟨N₁, hz₁, hs₁⟩ := sr_data hx
  obtain ⟨N₂, hz₂, hs₂⟩ := sr_data hy
  refine sr_of_shiftFinite (x * y) (min N₁ N₂) (fun m hm => ?_) ?_
  · rw [Pi.mul_apply, hz₁ m (lt_of_lt_of_le hm (min_le_left _ _)), zero_mul]
  · have : seqAt (x * y) (min N₁ N₂) = seqAt x (min N₁ N₂) * seqAt y (min N₁ N₂) := by funext m; rfl
    rw [this]; exact shiftFinite_mul (hs₁ _ (min_le_left _ _)) (hs₂ _ (min_le_right _ _))

theorem shiftFinite_zero : ShiftFinite (0 : ℕ → ℂ) :=
  ⟨⊥, inferInstance, fun f hf => by rw [(Submodule.mem_bot ℂ).1 hf, map_zero]; exact Submodule.zero_mem _, 0,
    fun k _ => by rw [map_zero]; exact Submodule.zero_mem _⟩

theorem shiftFinite_sum {ι : Type} (s : Finset ι) (f : ι → ℕ → ℂ) (h : ∀ i ∈ s, ShiftFinite (f i)) :
    ShiftFinite (fun m => ∑ i ∈ s, f i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact shiftFinite_zero
  | insert a s ha ih =>
    have : (fun m => ∑ i ∈ insert a s, f i m) = f a + fun m => ∑ i ∈ s, f i m := by
      funext m; rw [Finset.sum_insert ha]; rfl
    rw [this]
    exact shiftFinite_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem shiftFinite_geom (c α : ℂ) : ShiftFinite (fun m => c * α ^ m) := by
  let g : ℕ → ℂ := fun m => c * α ^ m
  refine ⟨Submodule.span ℂ {g}, FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _), ?_, 0, fun k _ => ?_⟩
  · intro f hf
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.mem_span_singleton.2 ⟨α, ?_⟩)
    funext n; simp only [sh_apply, Pi.smul_apply, smul_eq_mul, g, pow_succ]; ring
  · refine Submodule.mem_span_singleton.2 ⟨α ^ k, ?_⟩
    funext n; simp only [sh_apply, Pi.smul_apply, smul_eq_mul, g, pow_add]; ring

theorem shiftFinite_sh {s : ℕ → ℂ} (hs : ShiftFinite s) (j : ℕ) : ShiftFinite (sh j s) :=
  shiftFinite_of_eventually hs 0 j 0 (fun k _ => by rw [add_zero, sh_sh, add_comm])

theorem shiftFinite_seqAt_any {x : ℤ → ℂ} (hx : SR x) (N : ℤ) : ShiftFinite (seqAt x N) := by
  obtain ⟨N₀, -, hs⟩ := sr_data hx
  by_cases h : N ≤ N₀
  · exact hs N h
  · have e : seqAt x N = sh (N - N₀).toNat (seqAt x N₀) := by
      funext m; simp only [seqAt_apply, sh_apply]; congr 1
      have := Int.toNat_of_nonneg (show 0 ≤ N - N₀ by omega); push_cast; omega
    rw [e]; exact shiftFinite_sh (hs N₀ le_rfl) _

def boxLine (e₁ e₂ : ℕ) (w : ℕ → ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1), if e₁ * j + e₂ * l = m then w j l else 0

theorem finsum_line_eq_boxLine (w : ℤ × ℤ → ℂ) (N₁ N₂ : ℤ) (hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₂) → w n = 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂) (m : ℕ) :
    (∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = ((e₁ : ℤ) * N₁ + (e₂ : ℤ) * N₂) + (m : ℤ) then w n else 0) =
      boxLine e₁ e₂ (fun j l => w (N₁ + j, N₂ + l)) m := by
  classical
  set N : ℤ := (e₁ : ℤ) * N₁ + (e₂ : ℤ) * N₂ with hN
  let F : ℤ × ℤ → ℂ := fun n => if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = N + (m : ℤ) then w n else 0
  let B : Finset (ℤ × ℤ) := Finset.Icc N₁ (N₁ + m) ×ˢ Finset.Icc N₂ (N₂ + m)
  have hsupp : F.support ⊆ (B : Set (ℤ × ℤ)) := by
    intro n hn
    simp only [Function.mem_support, F, ne_eq, ite_eq_right_iff, not_forall, exists_prop] at hn
    obtain ⟨hl, hne⟩ := hn
    have hx1 : N₁ ≤ n.1 := by by_contra h; exact hne (hw _ (Or.inl (not_le.1 h)))
    have hy1 : N₂ ≤ n.2 := by by_contra h; exact hne (hw _ (Or.inr (not_le.1 h)))
    have he₁' : (1 : ℤ) ≤ e₁ := by exact_mod_cast he₁
    have he₂' : (1 : ℤ) ≤ e₂ := by exact_mod_cast he₂
    simp only [B, Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨hx1, ?_⟩, ⟨hy1, ?_⟩⟩ <;> nlinarith
  rw [finsum_eq_sum_of_support_subset F hsupp]

  have hB : B = (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).image
      (fun p : ℕ × ℕ => ((N₁ + p.1 : ℤ), (N₂ + p.2 : ℤ))) := by
    ext n
    simp only [B, Finset.mem_product, Finset.mem_Icc, Finset.mem_image, Finset.mem_range, Prod.ext_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      refine ⟨((n.1 - N₁).toNat, (n.2 - N₂).toNat), ⟨by omega, by omega⟩, ?_, ?_⟩
      · simp only; rw [Int.toNat_of_nonneg (by omega)]; ring
      · simp only; rw [Int.toNat_of_nonneg (by omega)]; ring
    · rintro ⟨p, ⟨h1, h2⟩, h3, h4⟩
      rw [← h3, ← h4]; omega
  rw [hB, Finset.sum_image (fun p _ q _ h => by
    simp only [Prod.ext_iff] at h; exact Prod.ext (by exact_mod_cast (add_left_cancel h.1)) (by exact_mod_cast (add_left_cancel h.2)))]
  rw [boxLine, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [F]
  have : ((e₁ : ℤ) * (N₁ + (p.1 : ℤ)) + (e₂ : ℤ) * (N₂ + (p.2 : ℤ)) = N + (m : ℤ)) ↔ (e₁ * p.1 + e₂ * p.2 = m) := by
    rw [hN]; constructor
    · intro h; have : ((e₁ * p.1 + e₂ * p.2 : ℕ) : ℤ) = m := by push_cast; linear_combination h
      exact_mod_cast this
    · intro h; have : ((e₁ * p.1 + e₂ * p.2 : ℕ) : ℤ) = m := by exact_mod_cast h
      push_cast at this; linear_combination this
  simp only [this]

theorem boxLine_sum {ι : Type} (e₁ e₂ : ℕ) (s : Finset ι) (w : ι → ℕ → ℕ → ℂ) (m : ℕ) :
    boxLine e₁ e₂ (fun j l => ∑ k ∈ s, w k j l) m = ∑ k ∈ s, boxLine e₁ e₂ (w k) m := by
  simp only [boxLine]
  have e1 : (∑ j ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
      (if e₁ * j + e₂ * l = m then ∑ k ∈ s, w k j l else 0)) =
      ∑ j ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1), ∑ k ∈ s, (if e₁ * j + e₂ * l = m then w k j l else 0) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [e1]
  have e2 : ∀ j ∈ Finset.range (m + 1), (∑ l ∈ Finset.range (m + 1), ∑ k ∈ s, (if e₁ * j + e₂ * l = m then w k j l else 0)) =
      ∑ k ∈ s, ∑ l ∈ Finset.range (m + 1), (if e₁ * j + e₂ * l = m then w k j l else 0) :=
    fun j _ => Finset.sum_comm
  rw [Finset.sum_congr rfl e2, Finset.sum_comm]

theorem boxLine_mul (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂) (p q : ℕ → ℂ) (m : ℕ) :
    boxLine e₁ e₂ (fun j l => p j * q l) m = convR (dil e₂ 0 q) (dil e₁ 0 p) m := by
  classical
  rw [boxLine, ← Finset.sum_product', convR_apply]
  have hrhs : ∀ i ∈ Finset.range (m + 1), dil e₁ 0 p i * dil e₂ 0 q (m - i) =
      if e₁ ∣ i ∧ e₂ ∣ (m - i) then p (i / e₁) * q ((m - i) / e₂) else 0 := by
    intro i hi
    simp only [dil_apply, add_zero]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl hrhs, ← Finset.sum_filter, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  symm
  refine Finset.sum_nbij' (fun i => (i / e₁, (m - i) / e₂)) (fun jl => e₁ * jl.1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨him, ⟨a, ha⟩, ⟨c, hc⟩⟩ := hi
    have ha' : i / e₁ = a := by rw [ha, Nat.mul_div_cancel_left _ he₁]
    have hc' : (m - i) / e₂ = c := by rw [hc, Nat.mul_div_cancel_left _ he₂]
    have hale : a ≤ i := by rw [ha]; exact Nat.le_mul_of_pos_left a he₁
    have hcle : c ≤ m - i := by rw [hc]; exact Nat.le_mul_of_pos_left c he₂
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, ha', hc']
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  · intro jl hjl
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hjl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hjl
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ⟨jl.1, rfl⟩, ?_⟩
    rw [show m - e₁ * jl.1 = e₂ * jl.2 by omega]; exact ⟨jl.2, rfl⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨him, ⟨a, ha⟩, -⟩ := hi
    simp only; rw [ha, Nat.mul_div_cancel_left _ he₁]
  · intro jl hjl
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hjl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hjl
    refine Prod.ext ?_ ?_
    · show e₁ * jl.1 / e₁ = jl.1; exact Nat.mul_div_cancel_left _ he₁
    · show (m - e₁ * jl.1) / e₂ = jl.2
      rw [show m - e₁ * jl.1 = e₂ * jl.2 by omega]; exact Nat.mul_div_cancel_left _ he₂
  · intro i hi; rfl

def solSpace (D : Polynomial ℂ) (K : ℕ) : Submodule ℂ (ℕ → ℂ) where
  carrier := {s | ∀ m, K ≤ m → ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * s (m - i) = 0}
  add_mem' := by
    intro s r hs hr m hm
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hs m hm, hr m hm, add_zero]
  zero_mem' := by intro m hm; simp
  smul_mem' := by
    intro c s hs m hm
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, hs m hm, mul_zero]

theorem solSpace_eq_zero (D : Polynomial ℂ) (hD : D.eval 0 ≠ 0) (K : ℕ) (hK : D.natDegree ≤ K)
    (s : ℕ → ℂ) (hs : s ∈ solSpace D K) (h0 : ∀ i, i < K → s i = 0) : s = 0 := by
  have hD0 : D.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  suffices key : ∀ m, s m = 0 from funext key
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < K
    · exact h0 m hm
    · have h := hs m (not_lt.1 hm)
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)] at h
      have hrest : ∑ i ∈ Finset.Ico 1 (D.natDegree + 1), D.coeff i * s (m - i) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
        have hi2 : i ≤ D.natDegree := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hi).2
        rw [ih (m - i) (by omega), mul_zero]
      rw [hrest, add_zero, Nat.sub_zero] at h
      exact (mul_eq_zero.1 h).elim (fun h0 => absurd h0 hD0) id

theorem exists_coord (D : Polynomial ℂ) (hD : D.eval 0 ≠ 0) (K : ℕ) (hK : D.natDegree ≤ K) :
    ∃ σ : Fin K → ℕ → ℂ, (∀ k, σ k ∈ solSpace D K) ∧ ∀ s ∈ solSpace D K, s = fun m => ∑ k : Fin K, s k * σ k m := by
  classical
  let S := solSpace D K
  let ρ : S →ₗ[ℂ] (Fin K → ℂ) :=
    { toFun := fun s => fun k => (s : ℕ → ℂ) k
      map_add' := fun s r => rfl
      map_smul' := fun c s => rfl }
  have hρ : Function.Injective ρ := by
    intro s r h
    apply Subtype.ext
    have := solSpace_eq_zero D hD K hK ((s : ℕ → ℂ) - r) (S.sub_mem s.2 r.2) (fun i hi => by
      have := congrFun h ⟨i, hi⟩; simp only [ρ, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [Pi.sub_apply, this, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ρ (LinearMap.ker_eq_bot.2 hρ)
  refine ⟨fun k => (g (Pi.single k 1) : ℕ → ℂ), fun k => (g (Pi.single k 1)).2, fun s hs => ?_⟩
  have h1 : g (ρ ⟨s, hs⟩) = ⟨s, hs⟩ := by
    have := congrArg (fun f => f ⟨s, hs⟩) hg; simpa using this
  have h2 : ρ ⟨s, hs⟩ = ∑ k : Fin K, s k • (Pi.single k (1 : ℂ) : Fin K → ℂ) := by
    funext k'
    simp only [ρ, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]; simp
  rw [h2, map_sum] at h1
  have h3 := congrArg (fun (w : S) => (w : ℕ → ℂ)) h1
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
  funext m
  have := congrFun h3 m
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem shiftFinite_of_mem_solSpace (D : Polynomial ℂ) (hD : D.eval 0 ≠ 0) (K : ℕ) (hK : D.natDegree ≤ K)
    (s : ℕ → ℂ) (hs : s ∈ solSpace D K) : ShiftFinite s := by

  let x : ℤ → ℂ := fun z => if 0 ≤ z then s z.toNat else 0
  have hx : seqAt x 0 = s := by
    funext m; simp only [seqAt_apply, zero_add, x, Int.natCast_nonneg, if_true, Int.toNat_natCast]
  rw [← hx]
  refine shiftFinite_of_rec x 0 D K hD fun m hm => ?_
  have h := hs m hm
  rw [← h]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := le_trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (le_trans hK hm)
  congr 1
  simp only [x, zero_add]
  rw [if_pos (by omega)]
  congr 1; omega

end ShellRec
p2m_reactivate "P2MW.S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.ShellRec"

namespace LineSums

theorem eq_zero_of_rec_all (g : ℤ → ℂ) (N : ℤ) (hN : ∀ m : ℤ, m < N → g m = 0) (D : Polynomial ℂ) (hD : D.eval 0 ≠ 0)
    (hrec : ∀ m : ℕ, ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * g (N + (m : ℤ) - (i : ℤ)) = 0) :
    ∀ m : ℤ, g m = 0 := by
  have hD0 : D.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]

  have key : ∀ m : ℕ, g (N + m) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      have h := hrec m
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)] at h
      have hrest : ∑ i ∈ Finset.Ico 1 (D.natDegree + 1), D.coeff i * g (N + (m : ℤ) - (i : ℤ)) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
        by_cases him : i ≤ m
        · have := ih (m - i) (by omega)
          rw [show N + (m : ℤ) - (i : ℤ) = N + ((m - i : ℕ) : ℤ) by push_cast; omega, this, mul_zero]
        · rw [hN _ (by push_cast; omega), mul_zero]
      rw [hrest, add_zero, Nat.cast_zero, sub_zero] at h
      exact (mul_eq_zero.1 h).elim (fun h0 => absurd h0 hD0) id
  intro m
  by_cases hm : m < N
  · exact hN m hm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = N + k := ⟨(m - N).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    exact key k

theorem row_rec (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ) (hD₁ : D₁.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)
    (z : ℤ) (m₂ : ℕ) (hm₂ : M ≤ m₂) :
    ∑ l ∈ Finset.range (D₂.natDegree + 1), D₂.coeff l * A (z, N₁ + (m₂ : ℤ) - (l : ℤ)) = 0 := by

  let g : ℤ → ℂ := fun z => ∑ l ∈ Finset.range (D₂.natDegree + 1), D₂.coeff l * A (z, N₁ + (m₂ : ℤ) - (l : ℤ))
  have hg : ∀ m : ℤ, g m = 0 := by
    refine eq_zero_of_rec_all g N₁ (fun m hm => ?_) D₁ hD₁ (fun m₁ => ?_)
    · simp only [g]
      exact Finset.sum_eq_zero fun l _ => by rw [hsupp _ (Or.inl hm), mul_zero]
    · have h := hrec m₁ m₂ (Or.inr hm₂)
      simp only [g, Finset.mul_sum, ← mul_assoc]
      exact h
  exact hg z

theorem col_rec (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ) (hD₂ : D₂.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0)
    (z : ℤ) (m₁ : ℕ) (hm₁ : M ≤ m₁) :
    ∑ i ∈ Finset.range (D₁.natDegree + 1), D₁.coeff i * A (N₁ + (m₁ : ℤ) - (i : ℤ), z) = 0 := by
  let g : ℤ → ℂ := fun z => ∑ i ∈ Finset.range (D₁.natDegree + 1), D₁.coeff i * A (N₁ + (m₁ : ℤ) - (i : ℤ), z)
  have hg : ∀ m : ℤ, g m = 0 := by
    refine eq_zero_of_rec_all g N₁ (fun m hm => ?_) D₂ hD₂ (fun m₂ => ?_)
    · simp only [g]
      exact Finset.sum_eq_zero fun i _ => by rw [hsupp _ (Or.inr hm), mul_zero]
    · have h := hrec m₁ m₂ (Or.inl hm₁)
      simp only [g, Finset.mul_sum]
      rw [Finset.sum_comm, ← h]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => by ring))
  exact hg z

end LineSums
p2m_reactivate "P2MW.S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.ShellRec"

end
p2m_reactivate "P2MW.S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.ShellRec"

open ShellRec LineSums in
theorem solution
    (A : ℤ × ℤ → ℂ) (b : ℤ → ℂ) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))
    (hb : ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → b m = 0) ∧
      (∀ m : ℕ, M' ≤ m →
        ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * b (N₂ + (m : ℤ) - (i : ℤ)) = 0)) :
    (∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧ (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) (N + (m : ℤ) - (i : ℤ)) = 0)) := by
  classical
  obtain ⟨N₁, D₁, D₂, M, hD₁, hD₂, hsupp, hrec⟩ := hA
  have hbSR : SR b := hb

  let w : ℤ × ℤ → ℂ := fun n => A n * b n.1 * α ^ n.1 * β ^ n.2
  have hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → w n = 0 := by
    intro n hn; simp only [w, hsupp n hn, zero_mul]
  set N : ℤ := (e₁ : ℤ) * N₁ + (e₂ : ℤ) * N₁ with hN

  set K := max M D₂.natDegree with hK
  obtain ⟨σ, hσ, hcoord⟩ := exists_coord D₂ hD₂ K (le_max_right _ _)
  have hrow : ∀ j : ℕ, (fun l : ℕ => A (N₁ + j, N₁ + l)) ∈ solSpace D₂ K := by
    intro j m hm
    have h := row_rec A N₁ D₁ D₂ M hD₁ hsupp hrec (N₁ + j) m (le_trans (le_max_left _ _) hm)
    rw [← h]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ m := le_trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)) (le_trans (le_max_right _ _) hm)
    congr 2; push_cast [Nat.cast_sub hl']; ring
  have hdec : ∀ j l : ℕ, A (N₁ + j, N₁ + l) = ∑ k : Fin K, A (N₁ + j, N₁ + ((k : ℕ) : ℤ)) * σ k l := by
    intro j l
    have := hcoord _ (hrow j)
    exact congrFun this l

  have hcolSF : ∀ k : ℕ, ShiftFinite (fun j : ℕ => A (N₁ + (j : ℤ), N₁ + (k : ℤ))) := fun k =>
    shiftFinite_of_rec (fun z => A (z, N₁ + k)) N₁ D₁ M hD₁
      (fun m hm => col_rec A N₁ D₁ D₂ M hD₂ hsupp hrec (N₁ + k) m hm)
  have hσSF : ∀ k, ShiftFinite (σ k) := fun k => shiftFinite_of_mem_solSpace D₂ hD₂ K (le_max_right _ _) _ (hσ k)
  have hbSF : ShiftFinite (seqAt b N₁) := shiftFinite_seqAt_any hbSR N₁
  have hαSF : ShiftFinite (fun j : ℕ => α ^ (N₁ + (j : ℤ))) := by
    have : (fun j : ℕ => α ^ (N₁ + (j : ℤ))) = fun j => α ^ N₁ * α ^ j := by
      funext j; rw [zpow_add₀ hα, zpow_natCast]
    rw [this]; exact shiftFinite_geom _ _
  have hβSF : ShiftFinite (fun l : ℕ => β ^ (N₁ + (l : ℤ))) := by
    have : (fun l : ℕ => β ^ (N₁ + (l : ℤ))) = fun l => β ^ N₁ * β ^ l := by
      funext l; rw [zpow_add₀ hβ, zpow_natCast]
    rw [this]; exact shiftFinite_geom _ _

  let p : Fin K → ℕ → ℂ := fun k j => A (N₁ + (j : ℤ), N₁ + ((k : ℕ) : ℤ)) * b (N₁ + j) * α ^ (N₁ + (j : ℤ))
  let q : Fin K → ℕ → ℂ := fun k l => σ k l * β ^ (N₁ + (l : ℤ))
  have hpSF : ∀ k, ShiftFinite (p k) := fun k =>
    shiftFinite_mul (shiftFinite_mul (hcolSF k) hbSF) hαSF
  have hqSF : ∀ k, ShiftFinite (q k) := fun k => shiftFinite_mul (hσSF k) hβSF

  have hline : seqAt (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) N =
      fun m => ∑ k : Fin K, convR (dil e₂ 0 (q k)) (dil e₁ 0 (p k)) m := by
    funext m
    rw [seqAt_apply]
    have h1 := finsum_line_eq_boxLine w N₁ N₁ hw e₁ e₂ he₁ he₂ m
    simp only [w] at h1
    rw [h1]
    have h2 : (fun j l : ℕ => A (N₁ + (j : ℤ), N₁ + (l : ℤ)) * b (N₁ + (j : ℤ)) * α ^ (N₁ + (j : ℤ)) * β ^ (N₁ + (l : ℤ))) =
        fun j l => ∑ k : Fin K, p k j * q k l := by
      funext j l
      simp only [p, q, hdec j l, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_; ring
    rw [h2, boxLine_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact boxLine_mul e₁ e₂ he₁ he₂ (p k) (q k) m

  refine sr_of_shiftFinite _ N (fun t ht => ?_) ?_
  · have : (fun n : ℤ × ℤ => if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) =
        fun _ => 0 := by
      funext n
      split_ifs with h
      · by_cases h1 : n.1 < N₁
        · rw [hsupp _ (Or.inl h1), zero_mul, zero_mul, zero_mul]
        · by_cases h2 : n.2 < N₁
          · rw [hsupp _ (Or.inr h2), zero_mul, zero_mul, zero_mul]
          · exfalso
            have he₁' : (0 : ℤ) ≤ e₁ := by exact_mod_cast he₁.le
            have he₂' : (0 : ℤ) ≤ e₂ := by exact_mod_cast he₂.le
            have : N ≤ t := by rw [← h, hN]; nlinarith
            exact absurd ht (not_lt.2 this)
      · rfl
    simp only [this, finsum_zero]
  · rw [hline]
    exact shiftFinite_sum _ _ fun k _ => shiftFinite_convR (shiftFinite_dil (hpSF k) e₁ he₁) (shiftFinite_dil (hqSF k) e₂ he₂)

end S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence
end P2MW
export P2MW.S_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence (solution)

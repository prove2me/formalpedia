-- Prove2me | solution 1 for ProxGapTight.theorem_3_3_small_weight
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T18:11:35.513216+00:00
-- url     : https://prove2.me/submissions/461d76a5-6bf6-4720-abef-239350e3e3ef

import Mathlib
import Definitions.Def_ProxGapTight_Um
import Definitions.Def_ProxGapTight_Lm
import Theorems.Thm_ProxGapTight_ad21_result_3_3_hyperplanes

section
/-!
q350 interface for reducing `theorem_3_3_small_weight` to the base case of
Adriaensen–Denaux (Result 3.3: hyperplanes of PG(k+1, q)) plus one AD21 §5 induction step
(n = k + 2, since a codimension-two subspace of F_Q^m is a k-space of PG(m-1, Q) with k = m-3).
Development only; nothing here is published.
-/

set_option autoImplicit false

namespace ProxGapTight.Dev.Q350
open ProxGapTight

/-- hyperplanes of `F^d` -/
def Hyp (K : Type) [Field K] (d : ℕ) : Type :=
  {H : Submodule K (Fin d → K) // Module.finrank K H + 1 = d}

/-- incidence vector of a hyperplane, on lines -/
noncomputable def incH (R : Type) [Semiring R] {K : Type} [Field K] {d : ℕ}
    (H : Hyp K d) : Lines K d → R := by
  classical
  exact fun ℓ => if ℓ.1 ≤ H.1 then 1 else 0

/-- the code of points and hyperplanes, `C_k(k+1, Q)` with `k = d - 2` -/
noncomputable def HypCode (K : Type) [Field K] (d p : ℕ) :
    Submodule (ZMod p) (Lines K d → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (fun H : Hyp K d => incH (ZMod p) H))

/-- **Base case** (AD21 Result 3.3 = [PZ18, Thm 1.4], [ADSW20, Cor 2.2.13]) at the cutoff
`L_m` with `m = d + 1`: in the code of points and hyperplanes of `F_Q^d`, every word of weight
at most `3Q^{d-2} - 3Q^{d-3} - 1` is a combination of at most two hyperplanes. -/
def BaseCase : Prop :=
  ∀ (p a : ℕ) [Fact p.Prime], 32 < p ^ a → p ^ a ≠ 49 → p ^ a ≠ 121 →
    ∀ d : ℕ, 3 ≤ d → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = p ^ a →
      ∀ v ∈ HypCode K d p, hammingNorm v ≤ Lm (p ^ a) (d + 1) →
        ∃ H H' : Hyp K d, ∃ α β : ZMod p, v = α • incH (ZMod p) H + β • incH (ZMod p) H'

/-- **Projection** from the line `R` (a point of PG(m-1, Q)), through an identification
`e : F^m / R ≃ F^(m-1)` (AD21 Remark 5.3: quotient geometry). The value at a line `λ` of the
quotient is the sum of `v` over the lines of the plane `R + λ`. -/
noncomputable def proj {K : Type} [Field K] [Fintype K] {m : ℕ} {p : ℕ}
    (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (v : Lines K m → ZMod p) : Lines K (m - 1) → ZMod p := by
  classical
  haveI := Fintype.ofFinite (Lines K m)
  exact fun lam => ∑ ℓ ∈ Finset.univ.filter
    (fun ℓ : Lines K m => ℓ.1 ≤ (lam.1.comap e.toLinearMap).comap R.1.mkQ), v ℓ

/-! ## Lines of a subspace -/

/-- the lines (projective points) inside a subspace -/
noncomputable def linesOf {K : Type} [Field K] [Fintype K] {m : ℕ}
    (U : Submodule K (Fin m → K)) : Finset (Lines K m) := by
  classical
  haveI := Fintype.ofFinite (Lines K m)
  exact Finset.univ.filter (fun ℓ => ℓ.1 ≤ U)


end ProxGapTight.Dev.Q350
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace ProxGapTight.Dev.Q350.Proj
open ProxGapTight ProxGapTight.Dev.Q350

section
variable {K : Type} [Field K] [Fintype K]

/-- lines of a subspace -/
noncomputable def linesIn {m : ℕ} (U : Submodule K (Fin m → K)) : Finset (Lines K m) := by
  classical
  exact Finset.univ.filter (fun ℓ => ℓ.1 ≤ U)

theorem mem_linesIn {m : ℕ} (U : Submodule K (Fin m → K)) (ℓ : Lines K m) :
    ℓ ∈ linesIn U ↔ ℓ.1 ≤ U := by
  classical
  simp [linesIn]

theorem card_linesIn {m : ℕ} (U : Submodule K (Fin m → K)) (d : ℕ)
    (hd : Module.finrank K U = d) :
    (linesIn U).card = (Fintype.card K ^ d - 1) / (Fintype.card K - 1) := by
  classical
  let f : Projectivization K U → Lines K m := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  haveI : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (linesIn U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_linesIn]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), hd, Nat.card_eq_fintype_card]
  rw [hc]

/-- `Q = p^a` vanishes in `ZMod p` -/
theorem card_cast_zero (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) :
    ((Fintype.card K : ℕ) : ZMod p) = 0 := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hK] at h1
    simp at h1
  rw [hK]
  push_cast
  rw [ZMod.natCast_self, zero_pow ha]

/-- the number of lines of a subspace is `1` mod `p` unless the subspace is zero -/
theorem card_linesIn_cast (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) {m : ℕ}
    (U : Submodule K (Fin m → K)) :
    ((linesIn U).card : ZMod p) = if U = ⊥ then 0 else 1 := by
  rw [card_linesIn U _ rfl]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [← Nat.geomSum_eq h2]
  push_cast
  rw [card_cast_zero p a hK]
  rcases Nat.eq_zero_or_pos (Module.finrank K U) with h | h
  · rw [h, if_pos (Submodule.finrank_eq_zero.mp h)]
    simp
  · have hne : U ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at h
      omega
    rw [if_neg hne]
    obtain ⟨n, hn⟩ : ∃ n, Module.finrank K U = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    rw [hn, Finset.sum_range_succ']
    simp

/-- a generator of a line -/
theorem line_rep {n : ℕ} (ℓ : Lines K n) :
    ∃ r : Fin n → K, r ≠ 0 ∧ r ∈ ℓ.1 ∧ (∀ y ∈ ℓ.1, ∃ c : K, c • r = y) ∧
      ∀ W : Submodule K (Fin n → K), ℓ.1 ≤ W ↔ r ∈ W := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp ℓ.2
  refine ⟨v.1, fun h => hv0 (Subtype.ext h), v.2, fun y hy => ?_,
    fun W => ⟨fun h => h v.2, fun h y hy => ?_⟩⟩
  · obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
    have : c • v.1 = y := congrArg Subtype.val hc
    rw [← this]
    exact W.smul_mem c h

theorem line_eq_of_le {n : ℕ} {ℓ ℓ' : Lines K n} (h : ℓ.1 ≤ ℓ'.1) : ℓ = ℓ' :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (by rw [ℓ.2, ℓ'.2]))

theorem line_ne_bot {n : ℕ} (ℓ : Lines K n) : ℓ.1 ≠ ⊥ := by
  intro h
  have := ℓ.2
  rw [h, finrank_bot] at this
  exact zero_ne_one this

theorem incH_of_le {p d : ℕ} (H : Hyp K d) (ℓ : Lines K d) (h : ℓ.1 ≤ H.1) :
    incH (ZMod p) H ℓ = 1 := by
  simp [incH, h]

theorem incH_of_not_le {p d : ℕ} (H : Hyp K d) (ℓ : Lines K d) (h : ¬ ℓ.1 ≤ H.1) :
    incH (ZMod p) H ℓ = 0 := by
  simp [incH, h]

variable {m : ℕ}

/-- the projection map `F^m → F^m / R ≃ F^(m-1)` -/
noncomputable def piR (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    (Fin m → K) →ₗ[K] (Fin (m - 1) → K) := e.toLinearMap ∘ₗ R.1.mkQ

/-- the plane `R + λ` -/
def P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : Submodule K (Fin m → K) :=
  (lam.1.comap e.toLinearMap).comap R.1.mkQ

theorem mem_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) (x : Fin m → K) : x ∈ P R e lam ↔ piR R e x ∈ lam.1 := Iff.rfl

theorem piR_eq_zero (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (x : Fin m → K) : piR R e x = 0 ↔ x ∈ R.1 := by
  simp [piR, Submodule.Quotient.mk_eq_zero]

theorem le_P_iff (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) (U : Submodule K (Fin m → K)) :
    U ≤ P R e lam ↔ U.map (piR R e) ≤ lam.1 := by
  rw [Submodule.map_le_iff_le_comap]
  rfl

theorem R_le_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : R.1 ≤ P R e lam := by
  intro x hx
  rw [mem_P, (piR_eq_zero R e x).mpr hx]
  exact lam.1.zero_mem

theorem finrank_map_line (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : Module.finrank K (ℓ.1.map (piR R e)) = 1 := by
  have h1 : Module.finrank K (ℓ.1.map (piR R e)) ≤ 1 := by
    have := Submodule.finrank_map_le (piR R e) ℓ.1
    rw [ℓ.2] at this
    exact this
  have h2 : ℓ.1.map (piR R e) ≠ ⊥ := by
    intro hb
    apply h
    apply line_eq_of_le
    intro x hx
    have hx' : piR R e x ∈ ℓ.1.map (piR R e) := Submodule.mem_map_of_mem hx
    rw [hb] at hx'
    exact (piR_eq_zero R e x).mp ((Submodule.mem_bot K).mp hx')
  have h3 : Module.finrank K (ℓ.1.map (piR R e)) ≠ 0 := by
    rwa [Ne, Submodule.finrank_eq_zero]
  omega

/-- the image line -/
noncomputable def lineMap (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : Lines K (m - 1) :=
  ⟨ℓ.1.map (piR R e), finrank_map_line R e ℓ h⟩

theorem le_P_iff_eq (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) (lam : Lines K (m - 1)) :
    ℓ.1 ≤ P R e lam ↔ lam = lineMap R e ℓ h := by
  rw [le_P_iff]
  constructor
  · intro hle
    exact (line_eq_of_le (ℓ := lineMap R e ℓ h) hle).symm
  · rintro rfl
    exact le_rfl

open Classical in
theorem proj_apply {p : ℕ} (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (v : Lines K m → ZMod p)
    (lam : Lines K (m - 1)) :
    proj R e v lam = ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Lines K m => ℓ.1 ≤ P R e lam), v ℓ := by
  unfold proj P
  rfl

end

/-! ## (4) weight -/

theorem chk_proj_weight_le {p : ℕ} {K : Type} [Field K] [Fintype K] {m : ℕ} (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (v : Lines K m → ZMod p)
    (hR : v R = 0) : hammingNorm (proj R e v) ≤ hammingNorm v := by
  classical
  unfold hammingNorm
  have key : ∀ lam ∈ Finset.univ.filter (fun lam => proj R e v lam ≠ 0),
      ∃ ℓ : Lines K m, ℓ.1 ≤ P R e lam ∧ v ℓ ≠ 0 := by
    intro lam hlam
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam
    rw [proj_apply] at hlam
    obtain ⟨ℓ, hℓ, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hlam
    exact ⟨ℓ, (Finset.mem_filter.mp hℓ).2, hv⟩
  haveI : Nonempty (Lines K m) := ⟨R⟩
  choose! f hf using key
  apply Finset.card_le_card_of_injOn f
  · intro lam hlam
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Finset.mem_coe] at hlam ⊢
    exact (hf lam (by simpa using hlam)).2
  · intro l1 h1 l2 h2 heq
    have h1' : l1 ∈ Finset.univ.filter (fun lam => proj R e v lam ≠ 0) := by simpa using h1
    have h2' : l2 ∈ Finset.univ.filter (fun lam => proj R e v lam ≠ 0) := by simpa using h2
    have hne : f l1 ≠ R := fun h => (hf l1 h1').2 (h ▸ hR)
    have a1 := (le_P_iff_eq R e (f l1) hne l1).1 (hf l1 h1').1
    have a2 := (le_P_iff_eq R e (f l1) hne l2).1 (heq ▸ (hf l2 h2').1)
    rw [a1, a2]

/-! ## (5) sum -/

theorem chk_proj_sum (p a : ℕ) [Fact p.Prime] {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 3 ≤ m) (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (v : Lines K m → ZMod p) :
    ∑ᶠ lam, proj R e v lam = ∑ᶠ ℓ, v ℓ := by
  classical
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [proj_apply, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  suffices h : ((Finset.univ.filter fun lam : Lines K (m - 1) => ℓ.1 ≤ P R e lam).card :
      ZMod p) = 1 by
    rw [h, one_mul]
  by_cases h : ℓ = R
  · subst h
    have hU : (Finset.univ.filter fun lam : Lines K (m - 1) => ℓ.1 ≤ P ℓ e lam) =
        linesIn (⊤ : Submodule K (Fin (m - 1) → K)) := by
      ext lam
      simp [mem_linesIn, R_le_P]
    rw [hU, card_linesIn_cast p a hK, if_neg]
    intro htop
    have := congrArg (fun U : Submodule K (Fin (m - 1) → K) => Module.finrank K U) htop
    simp only [finrank_top, Module.finrank_fin_fun, finrank_bot] at this
    omega
  · have hU : (Finset.univ.filter fun lam : Lines K (m - 1) => ℓ.1 ≤ P R e lam) =
        {lineMap R e ℓ h} := by
      ext lam
      simp [le_P_iff_eq R e ℓ h]
    rw [hU, Finset.card_singleton, Nat.cast_one]

/-! ## (2) membership -/

section mem
variable {K : Type} [Field K] [Fintype K]

/-- the hyperplane `ker φ` of a surjective functional -/
def kerHyp {d : ℕ} (φ : (Fin d → K) →ₗ[K] K) (hφ : Function.Surjective φ) : Hyp K d :=
  ⟨LinearMap.ker φ, by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.mpr hφ, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    omega⟩

/-- the all-ones vector is in the hyperplane code (sum over a pencil) -/
theorem ones_mem (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) {d : ℕ}
    (hd : 2 ≤ d) : (fun _ => (1 : ZMod p)) ∈ HypCode K d p := by
  classical
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have h01 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  let φ : K → (Fin d → K) →ₗ[K] K := fun c => LinearMap.proj i0 - c • LinearMap.proj i1
  let ψ : (Fin d → K) →ₗ[K] K := LinearMap.proj i1
  have hφ : ∀ c, Function.Surjective (φ c) := fun c t =>
    ⟨Pi.single i0 t, by simp [φ, Pi.single_apply, h01]⟩
  have hψ : Function.Surjective ψ := fun t => ⟨Pi.single i1 t, by simp [ψ]⟩
  have key : (fun _ => (1 : ZMod p)) =
      ∑ c : K, incH (ZMod p) (kerHyp (φ c) (hφ c)) + incH (ZMod p) (kerHyp ψ hψ) := by
    funext lam
    obtain ⟨r, hr0, -, -, hr⟩ := line_rep lam
    have hinc : ∀ (χ : (Fin d → K) →ₗ[K] K) (hχ : Function.Surjective χ),
        incH (ZMod p) (kerHyp χ hχ) lam = if χ r = 0 then 1 else 0 := by
      intro χ hχ
      by_cases h : χ r = 0
      · rw [if_pos h]; exact incH_of_le _ _ ((hr _).mpr h)
      · rw [if_neg h]; exact incH_of_not_le _ _ (fun h' => h ((hr _).mp h'))
    simp only [Finset.sum_apply, Pi.add_apply, hinc]
    rw [Finset.sum_boole]
    have hφr : ∀ c, φ c r = r i0 - c * r i1 := fun c => by simp [φ]
    have hψr : ψ r = r i1 := rfl
    by_cases h1 : r i1 = 0
    · rw [if_pos (show ψ r = 0 by rw [hψr]; exact h1)]
      by_cases h0 : r i0 = 0
      · have : (Finset.univ.filter fun c : K => φ c r = 0) = Finset.univ := by
          ext c; simp [hφr, h0, h1]
        rw [this, Finset.card_univ, card_cast_zero p a hK, zero_add]
      · have : (Finset.univ.filter fun c : K => φ c r = 0) = ∅ := by
          ext c; simp [hφr, h0, h1]
        rw [this]; simp
    · rw [if_neg (show ¬ ψ r = 0 by rw [hψr]; exact h1)]
      have : (Finset.univ.filter fun c : K => φ c r = 0) = {r i0 / r i1} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hφr]
        rw [sub_eq_zero, eq_div_iff h1, eq_comm]
      rw [this]; simp
  rw [key]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.subset_span ⟨_, rfl⟩)

/-- `proj` as a linear map -/
noncomputable def projL (p : ℕ) {m : ℕ} (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    (Lines K m → ZMod p) →ₗ[ZMod p] (Lines K (m - 1) → ZMod p) where
  toFun := proj R e
  map_add' v w := by
    funext lam
    simp only [proj_apply, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by
    funext lam
    simp only [proj_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

theorem proj_incVec (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) {m : ℕ}
    (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (W : Codim2 K m)
    (lam : Lines K (m - 1)) :
    proj R e (incVec (ZMod p) W) lam = if P R e lam ⊓ W.1 = ⊥ then 0 else 1 := by
  classical
  rw [proj_apply, ← card_linesIn_cast p a hK]
  have h1 : ∀ ℓ : Lines K m, incVec (ZMod p) W ℓ = if ℓ.1 ≤ W.1 then 1 else 0 := by
    intro ℓ
    by_cases h : ℓ.1 ≤ W.1 <;> simp [incVec, h]
  simp only [h1]
  rw [Finset.sum_boole, Finset.filter_filter]
  congr 2
  ext ℓ
  simp [mem_linesIn, le_inf_iff]

theorem gen_mem (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 3 ≤ m)
    (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (W : Codim2 K m) :
    proj R e (incVec (ZMod p) W) ∈ HypCode K (m - 1) p := by
  classical
  by_cases hRW : R.1 ≤ W.1
  · have : proj R e (incVec (ZMod p) W) = fun _ => 1 := by
      funext lam
      rw [proj_incVec p a hK, if_neg]
      intro hb
      apply line_ne_bot R
      rw [eq_bot_iff, ← hb]
      exact le_inf (R_le_P R e lam) hRW
    rw [this]
    exact ones_mem p a hK (by omega)
  · obtain ⟨r, hr0, hrR, hrmul, hr⟩ := line_rep R
    have hrW : r ∉ W.1 := fun h => hRW ((hr _).mpr h)
    have hinj : ∀ x ∈ W.1, piR R e x = 0 → x = 0 := by
      intro x hx h0
      obtain ⟨c, hc⟩ := hrmul x ((piR_eq_zero R e x).mp h0)
      by_cases hc0 : c = 0
      · rw [← hc, hc0, zero_smul]
      · exfalso
        apply hrW
        have : r = c⁻¹ • x := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [this]
        exact W.1.smul_mem _ hx
    let H : Submodule K (Fin (m - 1) → K) := W.1.map (piR R e)
    have hHf : Module.finrank K H + 1 = m - 1 := by
      have hi : Function.Injective ((piR R e).comp W.1.subtype) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro x hx
        exact Subtype.ext (hinj x.1 x.2 hx)
      have h1 := LinearMap.finrank_range_of_inj hi
      rw [LinearMap.range_comp, Submodule.range_subtype] at h1
      have := W.2
      change Module.finrank K H = _ at h1
      omega
    have : proj R e (incVec (ZMod p) W) = incH (ZMod p) (⟨H, hHf⟩ : Hyp K (m - 1)) := by
      funext lam
      rw [proj_incVec p a hK]
      obtain ⟨s, hs0, hslam, hsmul, hs⟩ := line_rep lam
      by_cases hl : lam.1 ≤ H
      · rw [incH_of_le (⟨H, hHf⟩ : Hyp K (m - 1)) lam hl, if_neg]
        obtain ⟨x, hxW, hx⟩ := Submodule.mem_map.mp (hl hslam)
        intro hb
        have hx0 : x ≠ 0 := by
          rintro rfl
          rw [map_zero] at hx
          exact hs0 hx.symm
        apply hx0
        have hmem : x ∈ P R e lam ⊓ W.1 := ⟨(mem_P R e lam x).mpr (by rw [hx]; exact hslam), hxW⟩
        rw [hb] at hmem
        exact (Submodule.mem_bot K).mp hmem
      · rw [incH_of_not_le (⟨H, hHf⟩ : Hyp K (m - 1)) lam hl, if_pos]
        rw [eq_bot_iff]
        rintro x ⟨hxP, hxW⟩
        rw [Submodule.mem_bot]
        by_contra hx0
        apply hl
        obtain ⟨c, hc⟩ := hsmul _ ((mem_P R e lam x).mp hxP)
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hc
          exact hx0 (hinj x hxW hc.symm)
        rw [hs]
        have : s = piR R e (c⁻¹ • x) := by
          rw [map_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [this]
        exact Submodule.mem_map_of_mem (W.1.smul_mem _ hxW)
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩

end mem

theorem chk_proj_mem (p a : ℕ) [Fact p.Prime] {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 3 ≤ m) (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    ∀ v ∈ Um K m p, proj R e v ∈ HypCode K (m - 1) p := by
  intro v hv
  have hle : Um K m p ≤ (HypCode K (m - 1) p).comap (projL p R e) := by
    unfold Um
    rw [Submodule.span_le]
    rintro _ ⟨W, rfl⟩
    exact gen_mem p a hK hm R e W
  exact hle hv

end ProxGapTight.Dev.Q350.Proj

namespace ProxGapTight.Dev.Q350
open ProxGapTight

theorem proj_mem : type_of% @Proj.chk_proj_mem := @Proj.chk_proj_mem
theorem proj_weight_le : type_of% @Proj.chk_proj_weight_le := @Proj.chk_proj_weight_le
theorem proj_sum : type_of% @Proj.chk_proj_sum := @Proj.chk_proj_sum

end ProxGapTight.Dev.Q350
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.Q350
open ProxGapTight

namespace Three

/-! ## Arithmetic of `θ_d = (Q^d - 1)/(Q - 1)` -/

/-- number of lines in a `d`-dimensional space over a field with `Q` elements -/
def th (Q d : ℕ) : ℕ := (Q ^ d - 1) / (Q - 1)

theorem th_dvd (Q d : ℕ) : (Q - 1) * th Q d = Q ^ d - 1 := by
  unfold th
  have : Q - 1 ∣ Q ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow Q 1 d
  exact Nat.mul_div_cancel' this

theorem th_succ (Q d : ℕ) (hQ : 2 ≤ Q) : th Q (d + 1) = Q ^ d + th Q d := by
  have h1 := th_dvd Q d
  have h2 := th_dvd Q (d + 1)
  have hP : 1 ≤ Q ^ d := Nat.one_le_pow _ _ (by omega)
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 2 := ⟨Q - 2, by omega⟩
  have e1 : Q' + 2 - 1 = Q' + 1 := by omega
  rw [e1] at h1 h2
  rw [pow_succ] at h2
  set P := (Q' + 2) ^ d
  have hr : (Q' + 1) * (P + th (Q' + 2) d) = (Q' + 1) * P + (P - 1) := by
    rw [Nat.mul_add, h1]
  have : (Q' + 1) * th (Q' + 2) (d + 1) = (Q' + 1) * (P + th (Q' + 2) d) := by
    rw [h2, hr]
    have : P * (Q' + 2) = (Q' + 1) * P + P := by ring
    omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

theorem th_small (Q d : ℕ) (hQ : 33 ≤ Q) : 32 * th Q d + 1 ≤ Q ^ d := by
  have h1 := th_dvd Q d
  have hP : 1 ≤ Q ^ d := Nat.one_le_pow _ _ (by omega)
  have : 32 * th Q d ≤ (Q - 1) * th Q d := Nat.mul_le_mul_right _ (by omega)
  omega

theorem th_mono (Q : ℕ) (hQ : 1 ≤ Q) {d d' : ℕ} (h : d ≤ d') : th Q d ≤ th Q d' := by
  unfold th
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right hQ h

/-! ## Finset counting -/

theorem piece {L : Type} [DecidableEq L] (X Y Z : Finset L) :
    (X \ (Y ∪ Z)).card + (X ∩ Y).card + (X ∩ Z).card = X.card + (X ∩ Y ∩ Z).card := by
  have h1 := Finset.card_sdiff_add_card_inter X (Y ∪ Z)
  have h2 : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := Finset.inter_union_distrib_left X Y Z
  have h3 := Finset.card_union_add_card_inter (X ∩ Y) (X ∩ Z)
  have h4 : (X ∩ Y) ∩ (X ∩ Z) = X ∩ Y ∩ Z := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [h2] at h1
  rw [h4] at h3
  omega

theorem card_union3 {L : Type} [DecidableEq L] (B1 B2 B3 : Finset L)
    (h12 : Disjoint B1 B2) (h13 : Disjoint B1 B3) (h23 : Disjoint B2 B3) :
    (B1 ∪ B2 ∪ B3).card = B1.card + B2.card + B3.card := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h13, h23⟩),
    Finset.card_union_of_disjoint h12]

theorem tri_count {L : Type} [DecidableEq L] (A1 A2 A3 : Finset L) :
    A1.card + A2.card + A3.card + 3 * (A1 ∩ A2 ∩ A3).card ≤
      ((A1 \ (A2 ∪ A3)) ∪ (A2 \ (A1 ∪ A3)) ∪ (A3 \ (A1 ∪ A2))).card +
        2 * ((A1 ∩ A2).card + (A1 ∩ A3).card + (A2 ∩ A3).card) := by
  have p1 := piece A1 A2 A3
  have p2 := piece A2 A1 A3
  have p3 := piece A3 A1 A2
  have c21 : (A2 ∩ A1).card = (A1 ∩ A2).card := by rw [Finset.inter_comm]
  have c31 : (A3 ∩ A1).card = (A1 ∩ A3).card := by rw [Finset.inter_comm]
  have c32 : (A3 ∩ A2).card = (A2 ∩ A3).card := by rw [Finset.inter_comm]
  have t2 : A2 ∩ A1 ∩ A3 = A1 ∩ A2 ∩ A3 := by
    ext x; simp only [Finset.mem_inter]; tauto
  have t3 : A3 ∩ A1 ∩ A2 = A1 ∩ A2 ∩ A3 := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [t2] at p2
  rw [t3] at p3
  have hd : ∀ (X Y Z : Finset L), Disjoint (X \ (Y ∪ Z)) (Y \ (X ∪ Z)) := by
    intro X Y Z
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx hy
    tauto
  have hd' : ∀ (X Y Z : Finset L), Disjoint (X \ (Y ∪ Z)) (Z \ (X ∪ Y)) := by
    intro X Y Z
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx hy
    tauto
  have hd'' : Disjoint (A2 \ (A1 ∪ A3)) (A3 \ (A1 ∪ A2)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx hy
    tauto
  rw [card_union3 _ _ _ (hd A1 A2 A3) (hd' A1 A2 A3) hd'']
  omega

/-! ## Lines of a subspace -/

section geoK
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

noncomputable def linesIn (U : Submodule K (Fin m → K)) : Finset (Lines K m) := by
  classical
  exact Finset.univ.filter (fun ℓ => ℓ.1 ≤ U)

theorem mem_linesIn (U : Submodule K (Fin m → K)) (ℓ : Lines K m) :
    ℓ ∈ linesIn U ↔ ℓ.1 ≤ U := by
  classical
  simp [linesIn]

theorem card_linesIn (U : Submodule K (Fin m → K)) (d : ℕ) (hd : Module.finrank K U = d) :
    (linesIn U).card = (Fintype.card K ^ d - 1) / (Fintype.card K - 1) := by
  classical
  let f : Projectivization K U → Lines K m := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  haveI : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (linesIn U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_linesIn]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), hd, Nat.card_eq_fintype_card]
  rw [hc]

theorem card_linesIn_th (U : Submodule K (Fin m → K)) :
    (linesIn U).card = th (Fintype.card K) (Module.finrank K U) :=
  card_linesIn U _ rfl

theorem linesIn_inf (U V : Submodule K (Fin m → K)) [DecidableEq (Lines K m)] :
    linesIn U ∩ linesIn V = linesIn (U ⊓ V) := by
  ext ℓ
  simp [mem_linesIn]

theorem finrank_inf_le (W W' : Codim2 K m) (hne : W ≠ W') :
    Module.finrank K ↥(W.1 ⊓ W'.1) + 3 ≤ m := by
  have hW := W.2
  have hW' := W'.2
  have h2 : Module.finrank K ↥(W.1 ⊓ W'.1) ≤ Module.finrank K W.1 :=
    Submodule.finrank_mono inf_le_left
  by_contra hcon
  have h3 : Module.finrank K ↥(W.1 ⊓ W'.1) = Module.finrank K W.1 := by omega
  have h4 : Module.finrank K ↥(W.1 ⊓ W'.1) = Module.finrank K W'.1 := by omega
  have e1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : W.1 ⊓ W'.1 ≤ W.1) h3
  have e2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : W.1 ⊓ W'.1 ≤ W'.1) h4
  exact hne (Subtype.ext (e1.symm.trans e2))

/-- two codim-3 subspaces of `W₁` meet in dimension at least `m - 4` -/
theorem finrank_triple (W₁ W₂ W₃ : Codim2 K m)
    (h12 : Module.finrank K ↥(W₁.1 ⊓ W₂.1) + 3 = m)
    (h13 : Module.finrank K ↥(W₁.1 ⊓ W₃.1) + 3 = m) :
    m ≤ Module.finrank K ↥(W₁.1 ⊓ W₂.1 ⊓ W₃.1) + 4 := by
  have hW := W₁.2
  have key := Submodule.finrank_sup_add_finrank_inf_eq (W₁.1 ⊓ W₂.1) (W₁.1 ⊓ W₃.1)
  have hsup : Module.finrank K ↥((W₁.1 ⊓ W₂.1) ⊔ (W₁.1 ⊓ W₃.1)) ≤ Module.finrank K W₁.1 :=
    Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  have hinf : Module.finrank K ↥((W₁.1 ⊓ W₂.1) ⊓ (W₁.1 ⊓ W₃.1)) ≤
      Module.finrank K ↥(W₁.1 ⊓ W₂.1 ⊓ W₃.1) := by
    apply Submodule.finrank_mono
    intro x hx
    simp only [Submodule.mem_inf] at hx ⊢
    tauto
  omega

end geoK

/-! ## The theorem -/

theorem chk_three_weight_gt (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 4 ≤ m) (W₁ W₂ W₃ : Codim2 K m)
    (α₁ α₂ α₃ : ZMod p)
    (h2 : ¬ ∃ W W' : Codim2 K m, ∃ α β : ZMod p,
      α₁ • incVec (ZMod p) W₁ + α₂ • incVec (ZMod p) W₂ + α₃ • incVec (ZMod p) W₃ =
        α • incVec (ZMod p) W + β • incVec (ZMod p) W') :
    Lm (p ^ a) m < hammingNorm
      (α₁ • incVec (ZMod p) W₁ + α₂ • incVec (ZMod p) W₂ + α₃ • incVec (ZMod p) W₃) := by
  classical
  -- nondegeneracy
  have ha1 : α₁ ≠ 0 := by
    rintro rfl; exact h2 ⟨W₂, W₃, α₂, α₃, by simp⟩
  have ha2 : α₂ ≠ 0 := by
    rintro rfl; exact h2 ⟨W₁, W₃, α₁, α₃, by simp⟩
  have ha3 : α₃ ≠ 0 := by
    rintro rfl; exact h2 ⟨W₁, W₂, α₁, α₂, by simp⟩
  have hn12 : W₁ ≠ W₂ := by
    rintro rfl; exact h2 ⟨W₁, W₃, α₁ + α₂, α₃, by rw [add_smul]⟩
  have hn13 : W₁ ≠ W₃ := by
    rintro rfl; exact h2 ⟨W₁, W₂, α₁ + α₃, α₂, by rw [add_smul]; abel⟩
  have hn23 : W₂ ≠ W₃ := by
    rintro rfl; exact h2 ⟨W₁, W₂, α₁, α₂ + α₃, by rw [add_smul]; abel⟩
  set v := α₁ • incVec (ZMod p) W₁ + α₂ • incVec (ZMod p) W₂ + α₃ • incVec (ZMod p) W₃ with hv
  set A1 := linesIn W₁.1
  set A2 := linesIn W₂.1
  set A3 := linesIn W₃.1
  -- the lines in exactly one subspace lie in the support
  have hsupp : ((A1 \ (A2 ∪ A3)) ∪ (A2 \ (A1 ∪ A3)) ∪ (A3 \ (A1 ∪ A2))) ⊆
      Finset.univ.filter (fun ℓ => v ℓ ≠ 0) := by
    intro ℓ hℓ
    simp only [Finset.mem_union, Finset.mem_sdiff, A1, A2, A3, mem_linesIn] at hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv, Pi.add_apply, Pi.smul_apply,
      incVec, smul_eq_mul]
    rcases hℓ with (⟨h1, h23⟩ | ⟨h1, h23⟩) | ⟨h1, h23⟩
    · simp only [not_or] at h23
      simp [h1, h23.1, h23.2, ha1]
    · simp only [not_or] at h23
      simp [h1, h23.1, h23.2, ha2]
    · simp only [not_or] at h23
      simp [h1, h23.1, h23.2, ha3]
  have hwt : ((A1 \ (A2 ∪ A3)) ∪ (A2 \ (A1 ∪ A3)) ∪ (A3 \ (A1 ∪ A2))).card ≤ hammingNorm v :=
    Finset.card_le_card hsupp
  have hcount := tri_count A1 A2 A3
  -- cardinalities
  set Q := Fintype.card K with hQdef
  have hQ33 : 33 ≤ Q := by omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
  have cA : ∀ W : Codim2 K (n + 4), (linesIn W.1).card = th Q (n + 2) := by
    intro W
    rw [card_linesIn_th]
    congr 1
    have := W.2
    omega
  have c12 : (A1 ∩ A2).card = th Q (Module.finrank K ↥(W₁.1 ⊓ W₂.1)) := by
    rw [linesIn_inf, card_linesIn_th]
  have c13 : (A1 ∩ A3).card = th Q (Module.finrank K ↥(W₁.1 ⊓ W₃.1)) := by
    rw [linesIn_inf, card_linesIn_th]
  have c23 : (A2 ∩ A3).card = th Q (Module.finrank K ↥(W₂.1 ⊓ W₃.1)) := by
    rw [linesIn_inf, card_linesIn_th]
  have cT : (A1 ∩ A2 ∩ A3).card = th Q (Module.finrank K ↥(W₁.1 ⊓ W₂.1 ⊓ W₃.1)) := by
    rw [linesIn_inf, linesIn_inf, card_linesIn_th]
  have d12 := finrank_inf_le W₁ W₂ hn12
  have d13 := finrank_inf_le W₁ W₃ hn13
  have d23 := finrank_inf_le W₂ W₃ hn23
  have hQ1 : 1 ≤ Q := by omega
  have I12 : (A1 ∩ A2).card ≤ th Q (n + 1) := by rw [c12]; exact th_mono Q hQ1 (by omega)
  have I13 : (A1 ∩ A3).card ≤ th Q (n + 1) := by rw [c13]; exact th_mono Q hQ1 (by omega)
  have I23 : (A2 ∩ A3).card ≤ th Q (n + 1) := by rw [c23]; exact th_mono Q hQ1 (by omega)
  -- arithmetic
  have s2 : th Q (n + 2) = Q ^ (n + 1) + th Q (n + 1) := th_succ Q (n + 1) (by omega)
  have s1 := th_succ Q n (by omega)
  have sm := th_small Q n hQ33
  have hM : 1 ≤ Q ^ n := Nat.one_le_pow _ _ (by omega)
  have hQM : Q ^ (n + 1) = Q * Q ^ n := by rw [pow_succ]; ring
  have h33 : 33 * Q ^ n ≤ Q * Q ^ n := Nat.mul_le_mul_right _ hQ33
  have hL : Lm (p ^ a) (n + 4) + 3 * Q ^ n + 1 = 3 * Q ^ (n + 1) := by
    unfold Lm
    rw [← hK, show n + 4 - 3 = n + 1 by omega, show n + 4 - 4 = n by omega]
    omega
  rw [cA W₁, cA W₂, cA W₃] at hcount
  by_cases hx : Module.finrank K ↥(W₁.1 ⊓ W₂.1) + 3 = n + 4 ∧
      Module.finrank K ↥(W₁.1 ⊓ W₃.1) + 3 = n + 4
  · -- all pairwise meets codim 3 through `W₁`: the triple meet has dim ≥ m - 4
    have hT := finrank_triple W₁ W₂ W₃ hx.1 hx.2
    have T : th Q n ≤ (A1 ∩ A2 ∩ A3).card := by rw [cT]; exact th_mono Q hQ1 (by omega)
    omega
  · -- some pairwise meet has dim ≤ m - 4
    have hsmall : (A1 ∩ A2).card ≤ th Q n ∨ (A1 ∩ A3).card ≤ th Q n := by
      by_cases h12 : Module.finrank K ↥(W₁.1 ⊓ W₂.1) + 3 = n + 4
      · right; rw [c13]; exact th_mono Q hQ1 (by omega)
      · left; rw [c12]; exact th_mono Q hQ1 (by omega)
    rcases hsmall with h | h <;> omega

end Three

end ProxGapTight.Dev.Q350

namespace ProxGapTight.Dev.Q350
open ProxGapTight

theorem three_weight_gt : type_of% @Three.chk_three_weight_gt := @Three.chk_three_weight_gt

end ProxGapTight.Dev.Q350
end

section
/-!
AD21 Lemma 5.6 (short and long secants), case `n = k + 2`, from the base case and the agreed
projection interface (`proj_mem`, `proj_weight_le`, `proj_sum`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace ProxGapTight.Dev.Q350.Secant
open ProxGapTight ProxGapTight.Dev.Q350

/-! ## Abstract combinatorics on the points of a line -/

section abstr
variable {α : Type} {p : ℕ}

/-- the conclusion of the base case on one line: short or long secant, and a `Q`-secant carries
one nonzero value -/
def Bp (L : Finset α) (Q : ℕ) (f : α → ZMod p) : Prop :=
  ((L.filter (fun x => f x ≠ 0)).card ≤ 2 ∨ Q ≤ (L.filter (fun x => f x ≠ 0)).card) ∧
  ((L.filter (fun x => f x ≠ 0)).card = Q →
    ∀ x ∈ L, ∀ y ∈ L, f x ≠ 0 → f y ≠ 0 → f x = f y)

theorem Bp_congr (L : Finset α) (Q : ℕ) (f g : α → ZMod p) (h : ∀ x ∈ L, f x = g x)
    (hf : Bp L Q f) : Bp L Q g := by
  have hfil : L.filter (fun x => g x ≠ 0) = L.filter (fun x => f x ≠ 0) :=
    Finset.filter_congr (fun x hx => by rw [h x hx])
  unfold Bp at hf ⊢
  rw [hfil]
  refine ⟨hf.1, fun hc x hx y hy hgx hgy => ?_⟩
  have := hf.2 hc x hx y hy (by rwa [h x hx]) (by rwa [h y hy])
  rwa [h x hx, h y hy] at this

theorem one_off (L : Finset α) (Q : ℕ) (hQ : 3 ≤ Q) (hL : L.card = Q + 1)
    (f : α → ZMod p) (b : α) (hb : b ∈ L) (v : ZMod p) (hf : ∀ x ∈ L, x ≠ b → f x = v) :
    Bp L Q f := by
  classical
  by_cases hv : v = 0
  · have hsub : L.filter (fun x => f x ≠ 0) ⊆ {b} := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_singleton]
      by_contra hxb
      exact hx.2 (by rw [hf x hx.1 hxb, hv])
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    exact ⟨Or.inl (by omega), fun h => by omega⟩
  · have hsub : L.erase b ⊆ L.filter (fun x => f x ≠ 0) := by
      intro x hx
      rw [Finset.mem_erase] at hx
      rw [Finset.mem_filter]
      exact ⟨hx.2, by rw [hf x hx.2 hx.1]; exact hv⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hb, hL] at h1
    refine ⟨Or.inr (by omega), fun hc x hx y hy hfx hfy => ?_⟩
    have hfb : f b = 0 := by
      by_contra hfb
      have : L.filter (fun x => f x ≠ 0) = L := Finset.filter_true_of_mem (fun x hx => by
        by_cases hxb : x = b
        · rw [hxb]; exact hfb
        · rw [hf x hx hxb]; exact hv)
      rw [this, hL] at hc
      omega
    have hxb : x ≠ b := fun h => hfx (h ▸ hfb)
    have hyb : y ≠ b := fun h => hfy (h ▸ hfb)
    rw [hf x hx hxb, hf y hy hyb]

theorem abs_two [DecidableEq α] (L A B : Finset α) (Q : ℕ) (hQ : 3 ≤ Q) (hL : L.card = Q + 1)
    (hAs : A ⊆ L) (hBs : B ⊆ L)
    (hA' : A = L ∨ A.card = 1) (hB' : B = L ∨ B.card = 1) (a b : ZMod p) (f : α → ZMod p)
    (hf : ∀ x ∈ L, f x = (if x ∈ A then a else 0) + (if x ∈ B then b else 0)) :
    Bp L Q f := by
  have hLne : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x0, hx0⟩ := hLne
  rcases hA' with hA | hA
  · rcases hB' with hB | hB
    · exact one_off L Q hQ hL f x0 hx0 (a + b) (fun x hx _ => by
        rw [hf x hx, hA, hB, if_pos hx, if_pos hx])
    · obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hB
      exact one_off L Q hQ hL f y (hBs (Finset.mem_singleton_self y)) a (fun x hx hxy => by
        rw [hf x hx, hA, if_pos hx, if_neg (by simpa using hxy), add_zero])
  · obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hA
    rcases hB' with hB | hB
    · exact one_off L Q hQ hL f y (hAs (Finset.mem_singleton_self y)) b (fun x hx hxy => by
        rw [hf x hx, hB, if_pos hx, if_neg (by simpa using hxy), zero_add])
    · obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hB
      have hsub : L.filter (fun x => f x ≠ 0) ⊆ {y, z} := by
        intro x hx
        rw [Finset.mem_filter] at hx
        by_contra hxyz
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxyz
        apply hx.2
        rw [hf x hx.1, if_neg (by simpa using hxyz.1), if_neg (by simpa using hxyz.2), add_zero]
      have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      rw [Finset.card_singleton] at this
      exact ⟨Or.inl this, fun h => by omega⟩

theorem abs_two_sum [DecidableEq α] (L A B : Finset α) (hAs : A ⊆ L) (hBs : B ⊆ L)
    (a b : ZMod p) (f : α → ZMod p)
    (hf : ∀ x ∈ L, f x = (if x ∈ A then a else 0) + (if x ∈ B then b else 0))
    (hAc : (A.card : ZMod p) = 1) (hBc : (B.card : ZMod p) = 1) :
    ∑ x ∈ L, f x = a + b := by
  rw [Finset.sum_congr rfl hf, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hAs, Finset.inter_eq_right.mpr hBs, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hAc, hBc, one_mul, one_mul]

theorem cnt_two [DecidableEq α] (L : Finset α) (c g : α → ZMod p) (P₁ P₂ : α) (h1 : P₁ ∈ L)
    (h2 : P₂ ∈ L) (h12 : P₁ ≠ P₂) (hg : ∀ x ∈ L, x ≠ P₁ → x ≠ P₂ → g x = c x) :
    (L.filter (fun x => g x ≠ 0)).card + (if c P₁ ≠ 0 then 1 else 0) +
        (if c P₂ ≠ 0 then 1 else 0) =
      (L.filter (fun x => c x ≠ 0)).card + (if g P₁ ≠ 0 then 1 else 0) +
        (if g P₂ ≠ 0 then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter]
  have h2' : P₂ ∈ L.erase P₁ := Finset.mem_erase.mpr ⟨h12.symm, h2⟩
  rw [← Finset.add_sum_erase L _ h1, ← Finset.add_sum_erase _ _ h2',
    ← Finset.add_sum_erase L _ h1, ← Finset.add_sum_erase _ _ h2']
  have : ∑ x ∈ (L.erase P₁).erase P₂, (if g x ≠ 0 then 1 else 0) =
      ∑ x ∈ (L.erase P₁).erase P₂, (if c x ≠ 0 then 1 else 0) :=
    Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_erase] at hx
      rw [hg x hx.2.2 hx.2.1 hx.1])
  rw [this]
  ring

/-- the core counting argument of AD21 Lemma 5.6: a secant with `2 ≤ t ≤ Q` cannot survive all
perturbations at one or two points. -/
theorem abs_pert [DecidableEq α] (L : Finset α) (Q : ℕ) (hQ : 7 ≤ Q) (hL : L.card = Q + 1)
    (c : α → ZMod p) (x₁ x₂ : ZMod p) (hx : x₁ ≠ 0) (Y : α)
    (hB : ∀ P₁ ∈ L, ∀ P₂ ∈ L, P₁ ≠ P₂ → P₁ ≠ Y → P₂ ≠ Y →
      Bp L Q (fun P => c P + (if P = P₁ then x₁ else 0) + (if P = P₂ then x₂ else 0)))
    (ht2 : 2 ≤ (L.filter (fun x => c x ≠ 0)).card)
    (htQ : (L.filter (fun x => c x ≠ 0)).card ≤ Q) : False := by
  set G : α → α → α → ZMod p :=
    fun P₁ P₂ P => c P + (if P = P₁ then x₁ else 0) + (if P = P₂ then x₂ else 0) with hGdef
  have hG1 : ∀ P₁ P₂ : α, P₁ ≠ P₂ → G P₁ P₂ P₁ = c P₁ + x₁ := by
    intro P₁ P₂ h; simp [G, h]
  have hG2 : ∀ P₁ P₂ : α, P₁ ≠ P₂ → G P₁ P₂ P₂ = c P₂ + x₂ := by
    intro P₁ P₂ h; simp [G, Ne.symm h]
  have hGo : ∀ P₁ P₂ P : α, P ≠ P₁ → P ≠ P₂ → G P₁ P₂ P = c P := by
    intro P₁ P₂ P h1 h2; simp [G, h1, h2]
  set Sp := L.filter (fun x => c x ≠ 0) with hSp
  set Z := L.filter (fun x => ¬ c x ≠ 0) with hZ
  have hcard : Sp.card + Z.card = Q + 1 := by
    rw [hSp, hZ, Finset.card_filter_add_card_filter_not, hL]
  have main : ∀ P₁ ∈ L, ∀ P₂ ∈ L, P₁ ≠ P₂ → P₁ ≠ Y → P₂ ≠ Y →
      ((L.filter (fun x => G P₁ P₂ x ≠ 0)).card + (if c P₁ ≠ 0 then 1 else 0) +
        (if c P₂ ≠ 0 then 1 else 0) =
      Sp.card + (if c P₁ + x₁ ≠ 0 then 1 else 0) + (if c P₂ + x₂ ≠ 0 then 1 else 0)) ∧
      Bp L Q (G P₁ P₂) := by
    intro P₁ h1 P₂ h2 h12 hY1 hY2
    refine ⟨?_, hB P₁ h1 P₂ h2 h12 hY1 hY2⟩
    have := cnt_two L c (G P₁ P₂) P₁ P₂ h1 h2 h12 (fun x _ hx1 hx2 => hGo P₁ P₂ x hx1 hx2)
    rw [hG1 P₁ P₂ h12, hG2 P₁ P₂ h12] at this
    exact this
  have memZ : ∀ x, x ∈ Z.erase Y ↔ x ≠ Y ∧ x ∈ L ∧ c x = 0 := by
    intro x; simp [hZ, Finset.mem_erase]
  have memS : ∀ x, x ∈ Sp.erase Y ↔ x ≠ Y ∧ x ∈ L ∧ c x ≠ 0 := by
    intro x; simp [hSp, Finset.mem_erase]
  have hZe := Finset.pred_card_le_card_erase (s := Z) (a := Y)
  have hSe := Finset.pred_card_le_card_erase (s := Sp) (a := Y)
  rcases (show Sp.card ≤ Q - 3 ∨ Sp.card = Q - 2 ∨ Sp.card = Q - 1 ∨ Sp.card = Q by omega)
    with h | h | h | h
  · obtain ⟨P₁, hP1, P₂, hP2, h12⟩ := Finset.one_lt_card.mp (show 1 < (Z.erase Y).card by omega)
    rw [memZ] at hP1 hP2
    obtain ⟨hc, hb⟩ := main P₁ hP1.2.1 P₂ hP2.2.1 h12 hP1.1 hP2.1
    rw [if_neg (not_not.mpr hP1.2.2), if_neg (not_not.mpr hP2.2.2), hP1.2.2, zero_add,
      if_pos hx] at hc
    have := hb.1
    split_ifs at hc <;> omega
  · obtain ⟨P₁, hP1⟩ := Finset.card_pos.mp (show 0 < (Z.erase Y).card by omega)
    obtain ⟨P₂, hP2⟩ := Finset.card_pos.mp (show 0 < (Sp.erase Y).card by omega)
    rw [memZ] at hP1
    rw [memS] at hP2
    have h12 : P₁ ≠ P₂ := fun h => hP2.2.2 (h ▸ hP1.2.2)
    obtain ⟨hc, hb⟩ := main P₁ hP1.2.1 P₂ hP2.2.1 h12 hP1.1 hP2.1
    rw [if_neg (not_not.mpr hP1.2.2), if_pos hP2.2.2, hP1.2.2, zero_add, if_pos hx] at hc
    have := hb.1
    split_ifs at hc <;> omega
  · obtain ⟨P₁, hP1, P₂, hP2, h12⟩ :=
      Finset.one_lt_card.mp (show 1 < (Sp.erase Y).card by omega)
    rw [memS] at hP1 hP2
    obtain ⟨hc, hb⟩ := main P₁ hP1.2.1 P₂ hP2.2.1 h12 hP1.1 hP2.1
    rw [if_pos hP1.2.2, if_pos hP2.2.2] at hc
    have := hb.1
    split_ifs at hc <;> omega
  · -- `t = Q`: four support points `A, B, C, D` off `Y`
    obtain ⟨A, hA, B, hB', hAB⟩ :=
      Finset.one_lt_card.mp (show 1 < (Sp.erase Y).card by omega)
    have hcd : 1 < (((Sp.erase Y).erase A).erase B).card := by
      have e1 := Finset.pred_card_le_card_erase (s := Sp.erase Y) (a := A)
      have e2 := Finset.pred_card_le_card_erase (s := (Sp.erase Y).erase A) (a := B)
      omega
    obtain ⟨C, hC, D, hD, hCD⟩ := Finset.one_lt_card.mp hcd
    rw [Finset.mem_erase, Finset.mem_erase] at hC hD
    have hCB := hC.1
    have hCA := hC.2.1
    have hDB := hD.1
    have hDA := hD.2.1
    have hCm : C ∈ Sp.erase Y := hC.2.2
    have hDm : D ∈ Sp.erase Y := hD.2.2
    rw [memS] at hA hB' hCm hDm
    -- the pair `(P₁, P₂)` gives a `Q`-secant, so the values agree off the perturbed points
    have pair : ∀ P₁ P₂ U V : α, P₁ ≠ P₂ → (P₁ ≠ Y ∧ P₁ ∈ L ∧ c P₁ ≠ 0) →
        (P₂ ≠ Y ∧ P₂ ∈ L ∧ c P₂ ≠ 0) → (U ∈ L ∧ c U ≠ 0) → (V ∈ L ∧ c V ≠ 0) →
        U ≠ P₁ → U ≠ P₂ → V ≠ P₁ → V ≠ P₂ → c U = c V ∧ c V = c P₁ + x₁ ∨ False := by
      intro P₁ P₂ U V h12 h1 h2 hU hV hU1 hU2 hV1 hV2
      obtain ⟨hc, hb⟩ := main P₁ h1.2.1 P₂ h2.2.1 h12 h1.1 h2.1
      rw [if_pos h1.2.2, if_pos h2.2.2] at hc
      have hb1 := hb.1
      have hb2 := hb.2
      by_cases g1 : c P₁ + x₁ ≠ 0
      · by_cases g2 : c P₂ + x₂ ≠ 0
        · rw [if_pos g1, if_pos g2] at hc
          have hN : (L.filter (fun x => G P₁ P₂ x ≠ 0)).card = Q := by omega
          have k1 := hb2 hN U hU.1 V hV.1 (by rw [hGo _ _ _ hU1 hU2]; exact hU.2)
            (by rw [hGo _ _ _ hV1 hV2]; exact hV.2)
          have k2 := hb2 hN V hV.1 P₁ h1.2.1 (by rw [hGo _ _ _ hV1 hV2]; exact hV.2)
            (by rw [hG1 _ _ h12]; exact g1)
          rw [hGo _ _ _ hU1 hU2, hGo _ _ _ hV1 hV2] at k1
          rw [hGo _ _ _ hV1 hV2, hG1 _ _ h12] at k2
          exact Or.inl ⟨k1, k2⟩
        · rw [if_pos g1, if_neg g2] at hc
          right; omega
      · rw [if_neg g1] at hc
        right
        split_ifs at hc <;> omega
    rcases pair A B D D hAB hA hB' ⟨hDm.2.1, hDm.2.2⟩ ⟨hDm.2.1, hDm.2.2⟩ hDA hDB hDA hDB
      with ⟨-, k1⟩ | hf
    · rcases pair B C A D (Ne.symm hCB) hB' hCm ⟨hA.2.1, hA.2.2⟩ ⟨hDm.2.1, hDm.2.2⟩
        hAB (Ne.symm hCA) hDB hCD.symm with ⟨k2, -⟩ | hf
      · apply hx
        have : c A = c A + x₁ := by rw [← k1]; exact k2
        exact (add_eq_left.mp this.symm)
      · exact hf
    · exact hf

end abstr

/-! ## Geometry helpers (copied from `Q350Proj.lean`, adapted to `linesOf`) -/

section geom
variable {K : Type} [Field K] [Fintype K]

theorem mem_linesOf {m : ℕ} (U : Submodule K (Fin m → K)) (ℓ : Lines K m) :
    ℓ ∈ linesOf U ↔ ℓ.1 ≤ U := by
  classical
  unfold linesOf
  simp

theorem card_linesOf {m : ℕ} (U : Submodule K (Fin m → K)) (d : ℕ)
    (hd : Module.finrank K U = d) :
    (linesOf U).card = (Fintype.card K ^ d - 1) / (Fintype.card K - 1) := by
  classical
  let f : Projectivization K U → Lines K m := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  haveI : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (linesOf U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_linesOf]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), hd, Nat.card_eq_fintype_card]
  rw [hc]

theorem card_cast_zero (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) :
    ((Fintype.card K : ℕ) : ZMod p) = 0 := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hK] at h1
    simp at h1
  rw [hK]
  push_cast
  rw [ZMod.natCast_self, zero_pow ha]

theorem card_linesOf_cast (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) {m : ℕ}
    (U : Submodule K (Fin m → K)) :
    ((linesOf U).card : ZMod p) = if U = ⊥ then 0 else 1 := by
  rw [card_linesOf U _ rfl]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [← Nat.geomSum_eq h2]
  push_cast
  rw [card_cast_zero p a hK]
  rcases Nat.eq_zero_or_pos (Module.finrank K U) with h | h
  · rw [h, if_pos (Submodule.finrank_eq_zero.mp h)]
    simp
  · have hne : U ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at h
      omega
    rw [if_neg hne]
    obtain ⟨n, hn⟩ : ∃ n, Module.finrank K U = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    rw [hn, Finset.sum_range_succ']
    simp

/-- a projective line has `Q + 1` points -/
theorem card_linesOf_two {m : ℕ} (U : Submodule K (Fin m → K)) (hU : Module.finrank K U = 2) :
    (linesOf U).card = Fintype.card K + 1 := by
  rw [card_linesOf U 2 hU]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨q, hq⟩ : ∃ q, Fintype.card K = q + 1 := ⟨Fintype.card K - 1, by omega⟩
  rw [hq]
  apply Nat.div_eq_of_eq_mul_left (by omega)
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

theorem card_linesOf_one {m : ℕ} (U : Submodule K (Fin m → K)) (hU : Module.finrank K U = 1) :
    (linesOf U).card = 1 := by
  rw [card_linesOf U 1 hU, pow_one]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  exact Nat.div_self (by omega)

theorem line_rep {n : ℕ} (ℓ : Lines K n) :
    ∃ r : Fin n → K, r ≠ 0 ∧ r ∈ ℓ.1 ∧ (∀ y ∈ ℓ.1, ∃ c : K, c • r = y) ∧
      ∀ W : Submodule K (Fin n → K), ℓ.1 ≤ W ↔ r ∈ W := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp ℓ.2
  refine ⟨v.1, fun h => hv0 (Subtype.ext h), v.2, fun y hy => ?_,
    fun W => ⟨fun h => h v.2, fun h y hy => ?_⟩⟩
  · obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
    have : c • v.1 = y := congrArg Subtype.val hc
    rw [← this]
    exact W.smul_mem c h

theorem line_gen {n : ℕ} (ℓ : Lines K n) : ∃ r : Fin n → K, r ≠ 0 ∧ ℓ.1 = K ∙ r := by
  obtain ⟨r, hr0, hrm, hmul, -⟩ := line_rep ℓ
  refine ⟨r, hr0, le_antisymm (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr hrm)⟩
  obtain ⟨c, rfl⟩ := hmul y hy
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)

theorem line_eq_of_le {n : ℕ} {ℓ ℓ' : Lines K n} (h : ℓ.1 ≤ ℓ'.1) : ℓ = ℓ' :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (by rw [ℓ.2, ℓ'.2]))

theorem incH_of_le {p d : ℕ} (H : Hyp K d) (ℓ : Lines K d) (h : ℓ.1 ≤ H.1) :
    incH (ZMod p) H ℓ = 1 := by
  simp [incH, h]

theorem incH_of_not_le {p d : ℕ} (H : Hyp K d) (ℓ : Lines K d) (h : ¬ ℓ.1 ≤ H.1) :
    incH (ZMod p) H ℓ = 0 := by
  simp [incH, h]

/-- the line spanned by a nonzero vector -/
def mkLine {m : ℕ} (v : Fin m → K) (hv : v ≠ 0) : Lines K m :=
  ⟨K ∙ v, finrank_span_singleton hv⟩

theorem line_inf {m : ℕ} (ℓ : Lines K m) (U : Submodule K (Fin m → K)) :
    ℓ.1 ≤ U ∨ ℓ.1 ⊓ U = ⊥ := by
  have h1 : Module.finrank K ↥(ℓ.1 ⊓ U) ≤ 1 := by
    have := Submodule.finrank_mono (inf_le_left : ℓ.1 ⊓ U ≤ ℓ.1)
    rw [ℓ.2] at this
    exact this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h | h
  · exact Or.inr (Submodule.finrank_eq_zero.mp h)
  · left
    have := Submodule.eq_of_le_of_finrank_eq (inf_le_left : ℓ.1 ⊓ U ≤ ℓ.1) (by rw [h, ℓ.2])
    rw [← this]; exact inf_le_right

theorem mem_line_iff {m : ℕ} (P₁ P : Lines K m) {a : Fin m → K} (ha : a ∈ P₁.1) (ha0 : a ≠ 0) :
    a ∈ P.1 ↔ P = P₁ := by
  constructor
  · intro h
    have e1 := line_eq_of_le (ℓ := mkLine a ha0) (ℓ' := P)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr h)
    have e2 := line_eq_of_le (ℓ := mkLine a ha0) (ℓ' := P₁)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr ha)
    rw [← e1, ← e2]
  · rintro rfl; exact ha

/-- the affine incidence in a plane `s ⊔ ⟨w⟩` -/
theorem incid {m : ℕ} {s : Submodule K (Fin m → K)} {w : Fin m → K} (hw : w ∉ s)
    {r y q : Fin m → K} (hr : r ∈ s) (hy : y ∈ s) (hq : q ∈ s) :
    w + y ∈ (K ∙ (w + r)) ⊔ (K ∙ q) ↔ y - r ∈ K ∙ q := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    by_cases ha : a = 1
    · subst ha
      rw [Submodule.mem_span_singleton]
      refine ⟨b, ?_⟩
      rw [one_smul] at huv
      calc b • q = (w + r + b • q) - (w + r) := by abel
        _ = y - r := by rw [huv]; abel
    · exfalso
      apply hw
      have key : (a - 1) • w = y - a • r - b • q := by
        rw [sub_smul, one_smul]
        rw [smul_add] at huv
        calc a • w - w = (a • w + a • r + b • q) - w - a • r - b • q := by abel
          _ = y - a • r - b • q := by rw [huv]; abel
      have h' : w = (a - 1)⁻¹ • (y - a • r - b • q) := by
        rw [← key, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr ha), one_smul]
      rw [h']
      exact s.smul_mem _ (s.sub_mem (s.sub_mem hy (s.smul_mem _ hr)) (s.smul_mem _ hq))
  · intro h
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h
    rw [Submodule.mem_sup]
    exact ⟨w + r, Submodule.mem_span_singleton_self _, b • q,
      Submodule.mem_span_singleton.mpr ⟨b, rfl⟩, by rw [hb]; abel⟩

theorem incidL {m : ℕ} {s : Submodule K (Fin m → K)} {w : Fin m → K} (hw : w ∉ s)
    {r y : Fin m → K} (hr : r ∈ s) (hy : y ∈ s) (Pl : Lines K m) (hPl : Pl.1 ≤ s) :
    (K ∙ (w + y)) ≤ (K ∙ (w + r)) ⊔ Pl.1 ↔ y - r ∈ Pl.1 := by
  obtain ⟨q, hq0, hPq⟩ := line_gen Pl
  have hq : q ∈ s := hPl (by rw [hPq]; exact Submodule.mem_span_singleton_self q)
  rw [hPq, Submodule.span_singleton_le_iff_mem]
  exact incid hw hr hy hq

theorem span_ne {m : ℕ} {s : Submodule K (Fin m → K)} {w : Fin m → K} (hw : w ∉ s)
    {r y : Fin m → K} (hr : r ∈ s) (hy : y ∈ s) (hne : y ≠ r) :
    (K ∙ (w + y)) ≠ K ∙ (w + r) := by
  intro h
  have h1 : w + y ∈ (K ∙ (w + r)) ⊔ (K ∙ (0 : Fin m → K)) := by
    rw [Submodule.span_zero_singleton, sup_bot_eq, ← h]
    exact Submodule.mem_span_singleton_self _
  rw [incid hw hr hy s.zero_mem, Submodule.span_zero_singleton, Submodule.mem_bot,
    sub_eq_zero] at h1
  exact hne h1

theorem aff_coord {m : ℕ} {s : Submodule K (Fin m → K)} {w : Fin m → K} (X : Lines K m)
    (hX : X.1 ≤ s ⊔ K ∙ w) (hXs : ¬ X.1 ≤ s) : ∃ y ∈ s, X.1 = K ∙ (w + y) := by
  obtain ⟨x, hx0, hX1⟩ := line_gen X
  have hx : x ∈ s ⊔ K ∙ w := hX (by rw [hX1]; exact Submodule.mem_span_singleton_self x)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hb : b ≠ 0 := by
    rintro rfl
    apply hXs
    rw [hX1, Submodule.span_singleton_le_iff_mem, ← huv, zero_smul, add_zero]; exact hu
  refine ⟨b⁻¹ • u, s.smul_mem _ hu, ?_⟩
  rw [hX1, ← huv]
  have : u + b • w = b • (w + b⁻¹ • u) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hb, one_smul, add_comm]
  rw [this, Submodule.span_singleton_smul_eq (IsUnit.mk0 b hb)]

end geom

/-! ## Projection helpers (copied from `Q350Proj.lean`) -/

section projsec
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

/-- the projection map `F^m → F^m / R ≃ F^(m-1)` -/
noncomputable def piR (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    (Fin m → K) →ₗ[K] (Fin (m - 1) → K) := e.toLinearMap ∘ₗ R.1.mkQ

/-- the plane `R + λ` -/
def P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : Submodule K (Fin m → K) :=
  (lam.1.comap e.toLinearMap).comap R.1.mkQ

theorem piR_eq_zero (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (x : Fin m → K) : piR R e x = 0 ↔ x ∈ R.1 := by
  simp [piR, Submodule.Quotient.mk_eq_zero]

theorem le_P_iff (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) (U : Submodule K (Fin m → K)) :
    U ≤ P R e lam ↔ U.map (piR R e) ≤ lam.1 := by
  rw [Submodule.map_le_iff_le_comap]
  rfl

theorem finrank_map_line (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : Module.finrank K (ℓ.1.map (piR R e)) = 1 := by
  have h1 : Module.finrank K (ℓ.1.map (piR R e)) ≤ 1 := by
    have := Submodule.finrank_map_le (piR R e) ℓ.1
    rw [ℓ.2] at this
    exact this
  have h2 : ℓ.1.map (piR R e) ≠ ⊥ := by
    intro hb
    apply h
    apply line_eq_of_le
    intro x hx
    have hx' : piR R e x ∈ ℓ.1.map (piR R e) := Submodule.mem_map_of_mem hx
    rw [hb] at hx'
    exact (piR_eq_zero R e x).mp ((Submodule.mem_bot K).mp hx')
  have h3 : Module.finrank K (ℓ.1.map (piR R e)) ≠ 0 := by
    rwa [Ne, Submodule.finrank_eq_zero]
  omega

/-- the image line -/
noncomputable def lineMap (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : Lines K (m - 1) :=
  ⟨ℓ.1.map (piR R e), finrank_map_line R e ℓ h⟩

theorem le_P_iff_eq (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) (lam : Lines K (m - 1)) :
    ℓ.1 ≤ P R e lam ↔ lam = lineMap R e ℓ h := by
  rw [le_P_iff]
  constructor
  · intro hle
    exact (line_eq_of_le (ℓ := lineMap R e ℓ h) hle).symm
  · rintro rfl
    exact le_rfl

open Classical in
theorem proj_apply {p : ℕ} (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (v : Lines K m → ZMod p)
    (lam : Lines K (m - 1)) :
    proj R e v lam = ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Lines K m => ℓ.1 ≤ P R e lam), v ℓ := by
  unfold proj P
  rfl

theorem P_lineMap (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : P R e (lineMap R e ℓ h) = R.1 ⊔ ℓ.1 := by
  have hker : LinearMap.ker (piR R e) = R.1 := by
    ext y; rw [LinearMap.mem_ker, piR_eq_zero]
  have : P R e (lineMap R e ℓ h) = (ℓ.1.map (piR R e)).comap (piR R e) := by
    ext x; rfl
  rw [this, Submodule.comap_map_eq, hker, sup_comm]

open Classical in
/-- the sum of `c` over the plane `R + P` -/
noncomputable def Gf {p : ℕ} (R : Lines K m) (c : Lines K m → ZMod p) (Pl : Lines K m) :
    ZMod p :=
  ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Lines K m => ℓ.1 ≤ R.1 ⊔ Pl.1), c ℓ

theorem proj_eq_G {p : ℕ} (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (c : Lines K m → ZMod p) (ℓ : Lines K m) (h : ℓ ≠ R) :
    proj R e c (lineMap R e ℓ h) = Gf R c ℓ := by
  classical
  rw [proj_apply]
  unfold Gf
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, P_lineMap]

end projsec

/-! ## The base case on one projective line -/

section base
variable {K : Type} [Field K] [Fintype K]

open Classical in
theorem hyp_sec {d : ℕ} (sb : Submodule K (Fin d → K)) (hsb : Module.finrank K sb = 2)
    (H : Hyp K d) :
    (linesOf sb).filter (fun ℓ => ℓ.1 ≤ H.1) = linesOf sb ∨
      ((linesOf sb).filter (fun ℓ => ℓ.1 ≤ H.1)).card = 1 := by
  classical
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq sb H.1
  have hle : Module.finrank K ↥(sb ⊔ H.1) ≤ d := by
    have := Submodule.finrank_le (sb ⊔ H.1); rwa [Module.finrank_fin_fun] at this
  have hH := H.2
  have hle2 : Module.finrank K ↥(sb ⊓ H.1) ≤ 2 := by
    have := Submodule.finrank_mono (inf_le_left : sb ⊓ H.1 ≤ sb)
    rwa [hsb] at this
  have hfil : (linesOf sb).filter (fun ℓ => ℓ.1 ≤ H.1) = linesOf (sb ⊓ H.1) := by
    ext ℓ; simp only [Finset.mem_filter, mem_linesOf, le_inf_iff]
  rcases (show Module.finrank K ↥(sb ⊓ H.1) = 1 ∨ Module.finrank K ↥(sb ⊓ H.1) = 2 by omega)
    with h | h
  · right; rw [hfil]; exact card_linesOf_one _ h
  · left
    have heq := Submodule.eq_of_le_of_finrank_eq (inf_le_left : sb ⊓ H.1 ≤ sb) (by rw [h, hsb])
    rw [hfil, heq]

/-- Lemma 5.6 in dimension `d` (`n = k + 1`), from the base case. -/
theorem base_sec (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) (hK : Fintype.card K = p ^ a) {d : ℕ} (hd : 3 ≤ d)
    (w : Lines K d → ZMod p) (hw : w ∈ HypCode K d p)
    (hwt : hammingNorm w ≤ Lm (p ^ a) (d + 1))
    (sb : Submodule K (Fin d → K)) (hsb : Module.finrank K sb = 2) :
    Bp (linesOf sb) (p ^ a) w ∧ ∑ ℓ ∈ linesOf sb, w ℓ = ∑ᶠ ℓ, w ℓ := by
  classical
  obtain ⟨H, H', α, β, rfl⟩ := hB p a hQ h49 h121 d hd K hK w hw hwt
  have hL : (linesOf sb).card = p ^ a + 1 := by rw [card_linesOf_two sb hsb, hK]
  obtain ⟨A, hA⟩ : ∃ A, A = (linesOf sb).filter (fun ℓ => ℓ.1 ≤ H.1) := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B, B = (linesOf sb).filter (fun ℓ => ℓ.1 ≤ H'.1) := ⟨_, rfl⟩
  have hf : ∀ x ∈ linesOf sb, (α • incH (ZMod p) H + β • incH (ZMod p) H') x =
      (if x ∈ A then α else 0) + (if x ∈ B then β else 0) := by
    intro x hx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hA, hB', Finset.mem_filter, hx,
      true_and]
    congr 1
    · by_cases h : x.1 ≤ H.1
      · rw [incH_of_le H x h, if_pos h, mul_one]
      · rw [incH_of_not_le H x h, if_neg h, mul_zero]
    · by_cases h : x.1 ≤ H'.1
      · rw [incH_of_le H' x h, if_pos h, mul_one]
      · rw [incH_of_not_le H' x h, if_neg h, mul_zero]
  have hcast : ∀ C : Finset (Lines K d), (C = linesOf sb ∨ C.card = 1) →
      (C.card : ZMod p) = 1 := by
    rintro C (rfl | h)
    · rw [hL, Nat.cast_add, ← hK, card_cast_zero p a hK, Nat.cast_one, zero_add]
    · rw [h, Nat.cast_one]
  have hsA := hyp_sec sb hsb H
  have hsB := hyp_sec sb hsb H'
  rw [← hA] at hsA
  rw [← hB'] at hsB
  have hAs : A ⊆ linesOf sb := by rw [hA]; exact Finset.filter_subset _ _
  have hBs : B ⊆ linesOf sb := by rw [hB']; exact Finset.filter_subset _ _
  refine ⟨abs_two (linesOf sb) A B (p ^ a) (by omega) hL hAs hBs hsA hsB α β _ hf, ?_⟩
  rw [abs_two_sum (linesOf sb) A B hAs hBs α β _ hf (hcast A hsA) (hcast B hsB)]
  have htot : ∀ H₀ : Hyp K d, ∑ ℓ, incH (ZMod p) H₀ ℓ = 1 := by
    intro H₀
    have : ∀ ℓ, incH (ZMod p) H₀ ℓ = if ℓ ∈ linesOf H₀.1 then 1 else 0 := by
      intro ℓ
      by_cases h : ℓ.1 ≤ H₀.1
      · rw [incH_of_le H₀ ℓ h, if_pos ((mem_linesOf _ _).mpr h)]
      · rw [incH_of_not_le H₀ ℓ h, if_neg (fun h' => h ((mem_linesOf _ _).mp h'))]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
      card_linesOf_cast p a hK, if_neg]
    intro hb
    have := H₀.2
    rw [hb, finrank_bot] at this
    omega
  rw [finsum_eq_sum_of_fintype]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htot, htot, mul_one, mul_one]

end base

/-! ## Transfer through a projection -/

section transfer
variable {K : Type} [Field K] [Fintype K]

theorem transfer (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 4 ≤ m)
    (c : Lines K m → ZMod p) (hc : c ∈ Um K m p) (hw : hammingNorm c ≤ Lm (p ^ a) m)
    (s : Submodule K (Fin m → K)) (hs : Module.finrank K s = 2) (R : Lines K m)
    (hRs : ¬ R.1 ≤ s) (hR : c R = 0) :
    Bp (linesOf s) (p ^ a) (Gf R c) ∧ ∑ ℓ ∈ linesOf s, Gf R c ℓ = ∑ᶠ ℓ, c ℓ := by
  classical
  have hRinf : R.1 ⊓ s = ⊥ := (line_inf R s).resolve_left hRs
  have hfq : Module.finrank K ((Fin m → K) ⧸ R.1) = Module.finrank K (Fin (m - 1) → K) := by
    have := Submodule.finrank_quotient_add_finrank R.1
    rw [R.2, Module.finrank_fin_fun] at this
    rw [Module.finrank_fin_fun]; omega
  let e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K) := LinearEquiv.ofFinrankEq _ _ hfq
  have hwm := proj_mem p a hK (by omega) R e c hc
  have hwt : hammingNorm (proj R e c) ≤ Lm (p ^ a) (m - 1 + 1) := by
    rw [show m - 1 + 1 = m by omega]; exact (proj_weight_le R e c hR).trans hw
  have hsb : Module.finrank K (s.map (piR R e)) = 2 := by
    have hinj : Function.Injective ((piR R e).comp s.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      apply Subtype.ext
      have h1 : (x : Fin m → K) ∈ R.1 ⊓ s := ⟨(piR_eq_zero R e x).mp hx, x.2⟩
      rw [hRinf] at h1
      exact (Submodule.mem_bot K).mp h1
    have h1 := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_comp, Submodule.range_subtype] at h1
    rw [h1, hs]
  obtain ⟨hBp, hsum⟩ :=
    base_sec hB p a hQ h49 h121 hK (d := m - 1) (by omega) _ hwm hwt _ hsb
  have hne : ∀ ℓ ∈ linesOf s, ℓ ≠ R := fun ℓ hℓ h => hRs (h ▸ (mem_linesOf _ _).mp hℓ)
  have hval : ∀ ℓ (hℓ : ℓ ∈ linesOf s), proj R e c (lineMap R e ℓ (hne ℓ hℓ)) = Gf R c ℓ :=
    fun ℓ hℓ => proj_eq_G R e c ℓ _
  have hmem : ∀ ℓ (hℓ : ℓ ∈ linesOf s), lineMap R e ℓ (hne ℓ hℓ) ∈ linesOf (s.map (piR R e)) := by
    intro ℓ hℓ
    rw [mem_linesOf]
    exact Submodule.map_mono ((mem_linesOf _ _).mp hℓ)
  have hinj : ∀ ℓ₁ (h₁ : ℓ₁ ∈ linesOf s) ℓ₂ (h₂ : ℓ₂ ∈ linesOf s),
      lineMap R e ℓ₁ (hne ℓ₁ h₁) = lineMap R e ℓ₂ (hne ℓ₂ h₂) → ℓ₁ = ℓ₂ := by
    intro ℓ₁ h₁ ℓ₂ h₂ heq
    have h1 : ℓ₁.1 ≤ P R e (lineMap R e ℓ₂ (hne ℓ₂ h₂)) := by
      rw [← heq]; exact (le_P_iff_eq R e ℓ₁ _ _).mpr rfl
    rw [P_lineMap] at h1
    apply line_eq_of_le
    have h3 : ℓ₁.1 ≤ (ℓ₂.1 ⊔ R.1) ⊓ s :=
      le_inf (by rw [sup_comm]; exact h1) ((mem_linesOf _ _).mp h₁)
    rw [sup_inf_assoc_of_le _ ((mem_linesOf _ _).mp h₂), hRinf, sup_bot_eq] at h3
    exact h3
  have hsurj : ∀ lam ∈ linesOf (s.map (piR R e)),
      ∃ ℓ, ∃ hℓ : ℓ ∈ linesOf s, lineMap R e ℓ (hne ℓ hℓ) = lam := by
    intro lam hlam
    obtain ⟨v, hv0, hlv⟩ := line_gen lam
    have hv : v ∈ s.map (piR R e) :=
      (mem_linesOf _ _).mp hlam (by rw [hlv]; exact Submodule.mem_span_singleton_self v)
    obtain ⟨x, hxs, hxv⟩ := Submodule.mem_map.mp hv
    have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hxv; exact hv0 hxv.symm
    have hxl : mkLine x hx0 ∈ linesOf s :=
      (mem_linesOf _ _).mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hxs)
    refine ⟨mkLine x hx0, hxl, line_eq_of_le ?_⟩
    show (K ∙ x).map (piR R e) ≤ lam.1
    rw [Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
      hxv, hlv]
    exact Submodule.mem_span_singleton_self v
  have hcard : ((linesOf s).filter (fun ℓ => Gf R c ℓ ≠ 0)).card =
      ((linesOf (s.map (piR R e))).filter (fun ℓ => proj R e c ℓ ≠ 0)).card := by
    apply Finset.card_bij (fun ℓ hℓ => lineMap R e ℓ (hne ℓ (Finset.mem_filter.mp hℓ).1))
    · intro ℓ hℓ
      rw [Finset.mem_filter] at hℓ ⊢
      exact ⟨hmem ℓ hℓ.1, by rw [hval ℓ hℓ.1]; exact hℓ.2⟩
    · intro ℓ₁ h₁ ℓ₂ h₂ heq
      exact hinj ℓ₁ (Finset.mem_filter.mp h₁).1 ℓ₂ (Finset.mem_filter.mp h₂).1 heq
    · intro lam hlam
      rw [Finset.mem_filter] at hlam
      obtain ⟨ℓ, hℓ, hℓe⟩ := hsurj lam hlam.1
      refine ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, ?_⟩, hℓe⟩
      rw [← hval ℓ hℓ, hℓe]; exact hlam.2
  have hsum' : ∑ ℓ ∈ linesOf s, Gf R c ℓ = ∑ lam ∈ linesOf (s.map (piR R e)), proj R e c lam :=
    Finset.sum_bij (fun ℓ hℓ => lineMap R e ℓ (hne ℓ hℓ)) hmem
      (fun ℓ₁ h₁ ℓ₂ h₂ heq => hinj ℓ₁ h₁ ℓ₂ h₂ heq) hsurj (fun ℓ hℓ => (hval ℓ hℓ).symm)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hcard]; exact hBp.1
  · intro hN x hx y hy hx0 hy0
    have := hBp.2 (by rw [← hcard]; exact hN) _ (hmem x hx) _ (hmem y hy)
      (by rw [hval x hx]; exact hx0) (by rw [hval y hy]; exact hy0)
    rwa [hval x hx, hval y hy] at this
  · rw [hsum', hsum, proj_sum p a hK (by omega) R e c]

end transfer

/-! ## A plane through `s` with at most two support points off `s` -/

section mainsec
variable {K : Type} [Field K] [Fintype K]

theorem geom_ge (Q n : ℕ) (hQ : 2 ≤ Q) : Q ^ n ≤ (Q ^ (n + 1) - 1) / (Q - 1) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h1 : 1 ≤ Q ^ n := Nat.one_le_pow _ _ (by omega)
  have h2 : Q ^ (n + 1) = Q ^ n * (Q - 1) + Q ^ n := by
    obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring
  generalize Q ^ n * (Q - 1) = X at h2 ⊢
  generalize Q ^ (n + 1) = Y at h2 ⊢
  omega

open Classical in
theorem plane_exists (p a : ℕ) (hQ : 32 < p ^ a) (hK : Fintype.card K = p ^ a) {m : ℕ}
    (hm : 4 ≤ m) (c : Lines K m → ZMod p) (hw : hammingNorm c ≤ Lm (p ^ a) m)
    (s : Submodule K (Fin m → K)) (hs : Module.finrank K s = 2) :
    ∃ w : Fin m → K, w ∉ s ∧
      ((linesOf (s ⊔ K ∙ w)).filter (fun ℓ => ¬ ℓ.1 ≤ s ∧ c ℓ ≠ 0)).card ≤ 2 := by
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl s
  have hTr : Module.finrank K T = m - 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hT
    rw [hs, Module.finrank_fin_fun] at this; omega
  have hsT : s ⊓ T = ⊥ := hT.inf_eq_bot
  choose wv hwv0 hwvmem hwvmul hwviff using fun τ : Lines K m => line_rep τ
  by_contra hcon
  push Not at hcon
  let F : Lines K m → Finset (Lines K m) := fun τ =>
    (linesOf (s ⊔ K ∙ wv τ)).filter (fun ℓ => ¬ ℓ.1 ≤ s ∧ c ℓ ≠ 0)
  have hwT : ∀ τ ∈ linesOf T, wv τ ∈ T := fun τ hτ => (mem_linesOf _ _).mp hτ (hwvmem τ)
  have hwvs : ∀ τ ∈ linesOf T, wv τ ∉ s := by
    intro τ hτ h
    have : wv τ ∈ s ⊓ T := ⟨h, hwT τ hτ⟩
    rw [hsT, Submodule.mem_bot] at this
    exact hwv0 τ this
  have hdisj : (↑(linesOf T) : Set (Lines K m)).PairwiseDisjoint F := by
    intro τ₁ h₁ τ₂ h₂ h12
    rw [Function.onFun, Finset.disjoint_left]
    intro ℓ hℓ1 hℓ2
    simp only [F, Finset.mem_filter, mem_linesOf] at hℓ1 hℓ2
    obtain ⟨x, hx0, hxl⟩ := line_gen ℓ
    have hxm : x ∈ ℓ.1 := by rw [hxl]; exact Submodule.mem_span_singleton_self x
    obtain ⟨u₁, hu₁, v₁, hv₁, e₁⟩ := Submodule.mem_sup.mp (hℓ1.1 hxm)
    obtain ⟨u₂, hu₂, v₂, hv₂, e₂⟩ := Submodule.mem_sup.mp (hℓ2.1 hxm)
    obtain ⟨b₁, rfl⟩ := Submodule.mem_span_singleton.mp hv₁
    obtain ⟨b₂, rfl⟩ := Submodule.mem_span_singleton.mp hv₂
    have hb₁ : b₁ ≠ 0 := by
      rintro rfl
      apply hℓ1.2.1
      rw [hxl, Submodule.span_singleton_le_iff_mem, ← e₁, zero_smul, add_zero]; exact hu₁
    have hdiff : b₁ • wv τ₁ - b₂ • wv τ₂ ∈ s ⊓ T := by
      constructor
      · have : b₁ • wv τ₁ - b₂ • wv τ₂ = u₂ - u₁ := by
          calc b₁ • wv τ₁ - b₂ • wv τ₂
              = (u₁ + b₁ • wv τ₁) - (u₂ + b₂ • wv τ₂) + u₂ - u₁ := by abel
            _ = u₂ - u₁ := by rw [e₁, e₂]; abel
        rw [this]; exact s.sub_mem hu₂ hu₁
      · exact T.sub_mem (T.smul_mem _ (hwT τ₁ h₁)) (T.smul_mem _ (hwT τ₂ h₂))
    rw [hsT, Submodule.mem_bot, sub_eq_zero] at hdiff
    have hin : wv τ₁ ∈ τ₂.1 := by
      have : wv τ₁ = (b₁⁻¹ * b₂) • wv τ₂ := by
        rw [mul_smul, ← hdiff, smul_smul, inv_mul_cancel₀ hb₁, one_smul]
      rw [this]; exact τ₂.1.smul_mem _ (hwvmem τ₂)
    exact h12 (line_eq_of_le ((hwviff τ₁ τ₂.1).mpr hin))
  have hsub : (linesOf T).biUnion F ⊆ Finset.univ.filter (fun ℓ => c ℓ ≠ 0) := by
    intro ℓ hℓ
    rw [Finset.mem_biUnion] at hℓ
    obtain ⟨τ, -, hℓ⟩ := hℓ
    simp only [F, Finset.mem_filter] at hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hℓ.2.2
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at h1
  have h2 : ∑ τ ∈ linesOf T, 3 ≤ ∑ τ ∈ linesOf T, (F τ).card :=
    Finset.sum_le_sum (fun τ hτ => hcon _ (hwvs τ hτ))
  rw [Finset.sum_const, smul_eq_mul] at h2
  have h3 := card_linesOf T _ hTr
  have h4 := geom_ge (Fintype.card K) (m - 3) (by rw [hK]; omega)
  rw [show m - 3 + 1 = m - 2 by omega, ← h3, hK] at h4
  have hh : hammingNorm c = (Finset.univ.filter (fun ℓ => c ℓ ≠ 0)).card := by
    unfold hammingNorm; congr
  unfold Lm at hw
  have h5 : 1 ≤ (p ^ a) ^ (m - 3) := Nat.one_le_pow _ _ (by omega)
  generalize (p ^ a) ^ (m - 3) = X at h4 h5 hw
  generalize (p ^ a) ^ (m - 4) = Y at hw
  omega

open Classical in
theorem Gf_formula {p m : ℕ} (c : Lines K m → ZMod p) (s σ : Submodule K (Fin m → K))
    (hsσ : s ≤ σ) (R : Lines K m) (hRσ : R.1 ≤ σ) (hRs : ¬ R.1 ≤ s) (_hR : c R = 0)
    (Pl : Lines K m) (hPl : Pl.1 ≤ s) :
    Gf R c Pl = c Pl + ∑ X ∈ (linesOf σ).filter (fun ℓ => ¬ ℓ.1 ≤ s ∧ c ℓ ≠ 0),
      (if X.1 ≤ R.1 ⊔ Pl.1 then c X else 0) := by
  have hRinf : R.1 ⊓ s = ⊥ := (line_inf R s).resolve_left hRs
  obtain ⟨E, hE⟩ : ∃ E, E = (linesOf σ).filter (fun ℓ => ¬ ℓ.1 ≤ s ∧ c ℓ ≠ 0) := ⟨_, rfl⟩
  rw [← hE]
  have hPE : Pl ∉ E := by
    intro h; rw [hE, Finset.mem_filter] at h; exact h.2.1 hPl
  unfold Gf
  have hsub : (insert Pl E).filter (fun ℓ => ℓ.1 ≤ R.1 ⊔ Pl.1) ⊆
      Finset.univ.filter (fun ℓ : Lines K m => ℓ.1 ≤ R.1 ⊔ Pl.1) :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  have hz : ∀ ℓ ∈ Finset.univ.filter (fun ℓ : Lines K m => ℓ.1 ≤ R.1 ⊔ Pl.1),
      ℓ ∉ (insert Pl E).filter (fun ℓ => ℓ.1 ≤ R.1 ⊔ Pl.1) → c ℓ = 0 := by
    intro ℓ h1 h2
    by_contra hc
    apply h2
    rw [Finset.mem_filter] at h1 ⊢
    refine ⟨?_, h1.2⟩
    rw [Finset.mem_insert]
    by_cases hls : ℓ.1 ≤ s
    · left
      apply line_eq_of_le
      have : ℓ.1 ≤ (Pl.1 ⊔ R.1) ⊓ s := le_inf (by rw [sup_comm]; exact h1.2) hls
      rwa [sup_inf_assoc_of_le _ hPl, hRinf, sup_bot_eq] at this
    · right
      rw [hE, Finset.mem_filter, mem_linesOf]
      exact ⟨h1.2.trans (sup_le hRσ (hPl.trans hsσ)), hls, hc⟩
  rw [← Finset.sum_subset hsub hz, Finset.sum_filter, Finset.sum_insert hPE,
    if_pos le_sup_right]

/-- the heart of AD21 Lemma 5.6 for a secant `s` with `2 ≤ t ≤ Q` -/
theorem key (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 4 ≤ m)
    (c : Lines K m → ZMod p) (hc : c ∈ Um K m p) (hw : hammingNorm c ≤ Lm (p ^ a) m)
    (s : Submodule K (Fin m → K)) (hs : Module.finrank K s = 2)
    (ht2 : 2 ≤ ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card)
    (htQ : ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≤ p ^ a) :
    Bp (linesOf s) (p ^ a) c ∧ ∑ ℓ ∈ linesOf s, c ℓ = ∑ᶠ ℓ, c ℓ := by
  classical
  obtain ⟨w, hws, hE⟩ := plane_exists p a hQ hK hm c hw s hs
  have hL : (linesOf s).card = p ^ a + 1 := by rw [card_linesOf_two s hs, hK]
  obtain ⟨E, hEdef⟩ : ∃ E, E =
      (linesOf (s ⊔ K ∙ w)).filter (fun ℓ => ¬ ℓ.1 ≤ s ∧ c ℓ ≠ 0) := ⟨_, rfl⟩
  rw [← hEdef] at hE
  have hsσ : s ≤ s ⊔ K ∙ w := le_sup_left
  have hwr0 : ∀ r ∈ s, w + r ≠ 0 := by
    intro r hr h
    apply hws
    have : w = -r := eq_neg_of_add_eq_zero_left h
    rw [this]; exact s.neg_mem hr
  have hRσ : ∀ r (hr : r ∈ s), (mkLine (w + r) (hwr0 r hr)).1 ≤ s ⊔ K ∙ w := by
    intro r hr
    show K ∙ (w + r) ≤ _
    rw [Submodule.span_singleton_le_iff_mem, add_comm]
    exact Submodule.add_mem_sup hr (Submodule.mem_span_singleton_self w)
  have hRs : ∀ r (hr : r ∈ s), ¬ (mkLine (w + r) (hwr0 r hr)).1 ≤ s := by
    intro r hr h
    apply hws
    have h1 : w + r ∈ s := (Submodule.span_singleton_le_iff_mem _ _).mp h
    have := s.sub_mem h1 hr
    rwa [add_sub_cancel_right] at this
  have hcoord : ∀ X ∈ E, ∃ y ∈ s, X.1 = K ∙ (w + y) := by
    intro X hX
    rw [hEdef, Finset.mem_filter, mem_linesOf] at hX
    exact aff_coord X hX.1 hX.2.1
  have hcX : ∀ X ∈ E, c X ≠ 0 := by
    intro X hX; rw [hEdef, Finset.mem_filter] at hX; exact hX.2.2
  have huniq : ∀ y ∈ s, ∀ y' ∈ s, (K ∙ (w + y)) = K ∙ (w + y') → y = y' :=
    fun y hy y' hy' h => by_contra (fun hne => span_ne hws hy' hy hne h)
  have hcR : ∀ r (hr : r ∈ s), (∀ X ∈ E, ∀ y ∈ s, X.1 = K ∙ (w + y) → y ≠ r) →
      c (mkLine (w + r) (hwr0 r hr)) = 0 := by
    intro r hr hne
    by_contra hc0
    have hmem : mkLine (w + r) (hwr0 r hr) ∈ E := by
      rw [hEdef, Finset.mem_filter, mem_linesOf]; exact ⟨hRσ r hr, hRs r hr, hc0⟩
    exact hne _ hmem r hr rfl rfl
  have hGf : ∀ r (hr : r ∈ s), c (mkLine (w + r) (hwr0 r hr)) = 0 → ∀ Pl ∈ linesOf s,
      Gf (mkLine (w + r) (hwr0 r hr)) c Pl =
        c Pl + ∑ X ∈ E, (if X.1 ≤ K ∙ (w + r) ⊔ Pl.1 then c X else 0) := by
    intro r hr hc0 Pl hPl
    rw [hEdef]
    exact Gf_formula c s _ hsσ _ (hRσ r hr) (hRs r hr) hc0 Pl ((mem_linesOf _ _).mp hPl)
  have hinc : ∀ r ∈ s, ∀ y ∈ s, ∀ X : Lines K m, X.1 = K ∙ (w + y) → ∀ Pl ∈ linesOf s,
      (X.1 ≤ K ∙ (w + r) ⊔ Pl.1 ↔ y - r ∈ Pl.1) := by
    intro r hr y hy X hX Pl hPl
    rw [hX]; exact incidL hws hr hy Pl ((mem_linesOf _ _).mp hPl)
  rcases (show E.card = 0 ∨ E.card = 1 ∨ E.card = 2 by omega) with h0 | h1 | h2
  · -- no support point of the plane off `s`: the projection keeps `c` on `s`
    rw [Finset.card_eq_zero] at h0
    have hR0 := hcR 0 s.zero_mem (by intro X hX; rw [h0] at hX; simp at hX)
    obtain ⟨hBp, hsum⟩ := transfer hB p a hQ h49 h121 hK hm c hc hw s hs _ (hRs 0 s.zero_mem) hR0
    have hG : ∀ Pl ∈ linesOf s, Gf (mkLine (w + 0) (hwr0 0 s.zero_mem)) c Pl = c Pl := by
      intro Pl hPl; rw [hGf 0 s.zero_mem hR0 Pl hPl, h0, Finset.sum_empty, add_zero]
    exact ⟨Bp_congr _ _ _ _ hG hBp, by rw [← hsum]; exact (Finset.sum_congr rfl hG).symm⟩
  · -- one support point `X₁` off `s`
    exfalso
    obtain ⟨X₁, hE1⟩ := Finset.card_eq_one.mp h1
    have hX1 : X₁ ∈ E := by rw [hE1]; exact Finset.mem_singleton_self _
    obtain ⟨y₁, hy₁, hX₁⟩ := hcoord X₁ hX1
    refine abs_pert (linesOf s) (p ^ a) (by omega) hL c (c X₁) 0 (hcX X₁ hX1) X₁ ?_ ht2 htQ
    intro P₁ hP₁ P₂ hP₂ h12 _ _
    obtain ⟨q₁, hq0, hPq⟩ := line_gen P₁
    have hq₁m : q₁ ∈ P₁.1 := by rw [hPq]; exact Submodule.mem_span_singleton_self q₁
    have hq₁ : q₁ ∈ s := (mem_linesOf _ _).mp hP₁ hq₁m
    have hr : y₁ - q₁ ∈ s := s.sub_mem hy₁ hq₁
    have e1 : y₁ - (y₁ - q₁) = q₁ := sub_sub_cancel _ _
    have hR0 : c (mkLine (w + (y₁ - q₁)) (hwr0 _ hr)) = 0 := by
      apply hcR _ hr
      intro X hX y hy hXy hyr
      rw [hE1, Finset.mem_singleton] at hX
      subst hX
      have := huniq y hy y₁ hy₁ (hXy.symm.trans hX₁)
      exact hq0 (by rw [← e1, sub_eq_zero]; exact this.symm.trans hyr)
    obtain ⟨hBp, -⟩ := transfer hB p a hQ h49 h121 hK hm c hc hw s hs _ (hRs _ hr) hR0
    refine Bp_congr _ _ _ _ (fun Pl hPl => ?_) hBp
    have i1 : X₁.1 ≤ K ∙ (w + (y₁ - q₁)) ⊔ Pl.1 ↔ Pl = P₁ := by
      rw [hinc _ hr y₁ hy₁ X₁ hX₁ Pl hPl, e1]; exact mem_line_iff P₁ Pl hq₁m hq0
    have t1 : (if X₁.1 ≤ K ∙ (w + (y₁ - q₁)) ⊔ Pl.1 then c X₁ else 0) =
        (if Pl = P₁ then c X₁ else 0) := by
      by_cases q : Pl = P₁
      · rw [if_pos (i1.mpr q), if_pos q]
      · rw [if_neg (fun h => q (i1.mp h)), if_neg q]
    rw [hGf _ hr hR0 Pl hPl, hE1, Finset.sum_singleton, t1, ite_self, add_zero]
  · -- two support points `X₁, X₂` off `s`
    exfalso
    obtain ⟨X₁, X₂, hX12, hE2⟩ := Finset.card_eq_two.mp h2
    have hX1 : X₁ ∈ E := by rw [hE2]; simp
    have hX2 : X₂ ∈ E := by rw [hE2]; simp
    obtain ⟨y₁, hy₁, hX₁⟩ := hcoord X₁ hX1
    obtain ⟨y₂, hy₂, hX₂⟩ := hcoord X₂ hX2
    have hy12 : y₁ - y₂ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      subst h
      exact hX12 (Subtype.ext (hX₁.trans hX₂.symm))
    refine abs_pert (linesOf s) (p ^ a) (by omega) hL c (c X₁) (c X₂) (hcX X₁ hX1)
      (mkLine (y₁ - y₂) hy12) ?_ ht2 htQ
    intro P₁ hP₁ P₂ hP₂ h12 hY1 hY2
    have hP₁s := (mem_linesOf _ _).mp hP₁
    have hP₂s := (mem_linesOf _ _).mp hP₂
    have hinf : P₁.1 ⊓ P₂.1 = ⊥ :=
      (line_inf P₁ P₂.1).resolve_left (fun h => h12 (line_eq_of_le h))
    have hsup : P₁.1 ⊔ P₂.1 = s := by
      apply Submodule.eq_of_le_of_finrank_eq (sup_le hP₁s hP₂s)
      have := Submodule.finrank_sup_add_finrank_inf_eq P₁.1 P₂.1
      rw [hinf, finrank_bot, P₁.2, P₂.2] at this
      rw [hs]; omega
    have hys : y₁ - y₂ ∈ P₁.1 ⊔ P₂.1 := by rw [hsup]; exact s.sub_mem hy₁ hy₂
    obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := Submodule.mem_sup.mp hys
    have hYm : y₁ - y₂ ∈ (mkLine (y₁ - y₂) hy12).1 := Submodule.mem_span_singleton_self _
    have ha₁0 : a₁ ≠ 0 := by
      rintro rfl
      rw [zero_add] at ha
      exact hY2 ((mem_line_iff (mkLine (y₁ - y₂) hy12) P₂ hYm hy12).mp (ha ▸ ha₂))
    have ha₂0 : a₂ ≠ 0 := by
      rintro rfl
      rw [add_zero] at ha
      exact hY1 ((mem_line_iff (mkLine (y₁ - y₂) hy12) P₁ hYm hy12).mp (ha ▸ ha₁))
    have hr : y₁ - a₁ ∈ s := s.sub_mem hy₁ (hP₁s ha₁)
    have e1 : y₁ - (y₁ - a₁) = a₁ := sub_sub_cancel _ _
    have e2 : y₂ - (y₁ - a₁) = -a₂ := by
      have : y₁ = y₂ + (a₁ + a₂) := by rw [ha]; abel
      rw [this]; abel
    have hR0 : c (mkLine (w + (y₁ - a₁)) (hwr0 _ hr)) = 0 := by
      apply hcR _ hr
      intro X hX y hy hXy hyr
      rw [hE2, Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl
      · have := huniq y hy y₁ hy₁ (hXy.symm.trans hX₁)
        exact ha₁0 (by rw [← e1, sub_eq_zero]; exact this.symm.trans hyr)
      · have := huniq y hy y₂ hy₂ (hXy.symm.trans hX₂)
        exact ha₂0 (by rw [← neg_eq_zero, ← e2, sub_eq_zero]; exact this.symm.trans hyr)
    obtain ⟨hBp, -⟩ := transfer hB p a hQ h49 h121 hK hm c hc hw s hs _ (hRs _ hr) hR0
    refine Bp_congr _ _ _ _ (fun Pl hPl => ?_) hBp
    have i1 : X₁.1 ≤ K ∙ (w + (y₁ - a₁)) ⊔ Pl.1 ↔ Pl = P₁ := by
      rw [hinc _ hr y₁ hy₁ X₁ hX₁ Pl hPl, e1]; exact mem_line_iff P₁ Pl ha₁ ha₁0
    have i2 : X₂.1 ≤ K ∙ (w + (y₁ - a₁)) ⊔ Pl.1 ↔ Pl = P₂ := by
      rw [hinc _ hr y₂ hy₂ X₂ hX₂ Pl hPl, e2, Submodule.neg_mem_iff]
      exact mem_line_iff P₂ Pl ha₂ ha₂0
    have t1 : (if X₁.1 ≤ K ∙ (w + (y₁ - a₁)) ⊔ Pl.1 then c X₁ else 0) =
        (if Pl = P₁ then c X₁ else 0) := by
      by_cases q : Pl = P₁
      · rw [if_pos (i1.mpr q), if_pos q]
      · rw [if_neg (fun h => q (i1.mp h)), if_neg q]
    have t2 : (if X₂.1 ≤ K ∙ (w + (y₁ - a₁)) ⊔ Pl.1 then c X₂ else 0) =
        (if Pl = P₂ then c X₂ else 0) := by
      by_cases q : Pl = P₂
      · rw [if_pos (i2.mpr q), if_pos q]
      · rw [if_neg (fun h => q (i2.mp h)), if_neg q]
    rw [hGf _ hr hR0 Pl hPl, hE2, Finset.sum_pair hX12, t1, t2, add_assoc]

end mainsec

/-! ## AD21 Lemma 5.6 -/

theorem chk_secant (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 4 ≤ m) (c : Lines K m → ZMod p)
    (hc : c ∈ Um K m p) (hw : hammingNorm c ≤ Lm (p ^ a) m)
    (s : Submodule K (Fin m → K)) (hs : Module.finrank K s = 2) :
    (((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≤ 2 ∨
        p ^ a ≤ ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card) ∧
      (((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card = 2 →
        ∑ ℓ ∈ linesOf s, c ℓ = ∑ᶠ ℓ, c ℓ) ∧
      (((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card = p ^ a →
        ∑ ℓ ∈ linesOf s, c ℓ = 0) := by
  have hL : (linesOf s).card = p ^ a + 1 := by rw [card_linesOf_two s hs, hK]
  have htle : ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≤ p ^ a + 1 := by
    rw [← hL]; exact Finset.card_filter_le _ _
  by_cases hsmall : ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≤ 1 ∨
      ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card = p ^ a + 1
  · refine ⟨by omega, fun h => by omega, fun h => by omega⟩
  push Not at hsmall
  obtain ⟨hB0, hsum⟩ := key hB p a hQ h49 h121 hK hm c hc hw s hs (by omega) (by omega)
  refine ⟨hB0.1, fun _ => hsum, fun hQt => ?_⟩
  obtain ⟨x0, hx0⟩ : ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).Nonempty :=
    Finset.card_pos.mp (by omega)
  rw [Finset.mem_filter] at hx0
  rw [← Finset.sum_filter_ne_zero, Finset.sum_congr rfl (fun y hy =>
    hB0.2 hQt y (Finset.mem_filter.mp hy).1 x0 hx0.1 (Finset.mem_filter.mp hy).2 hx0.2),
    Finset.sum_const, hQt, nsmul_eq_mul]
  have : ((p ^ a : ℕ) : ZMod p) = 0 := by rw [← hK]; exact card_cast_zero p a hK
  rw [this, zero_mul]

end ProxGapTight.Dev.Q350.Secant

namespace ProxGapTight.Dev.Q350
open ProxGapTight

theorem secant : type_of% @Secant.chk_secant := @Secant.chk_secant

end ProxGapTight.Dev.Q350
end

section
/-!
q350, AD21 Lemma 5.8 (case `n = k + 2`), case (2) only: `proj_R c = α₁ κ₁ + α₂ κ₂`,
`κ₁ ≠ κ₂`, `α₁, α₂ ≠ 0`.

Notation: `λᵢ = piR⁻¹ κᵢ` (hyperplanes of `F^m` through `R`), `τ = piR⁻¹ (κ₁ ∩ κ₂)`.

* Observation 1 (`tangent`, `tanM`): for every point `μ ∈ κ₁ \ κ₂` the plane `R + μ` meets
  `supp c` in exactly one point, of value `α₁`.
* The count (`finish`): if every point of `supp c ∩ (λ₁ \ τ)` lies in one codimension-two
  subspace `W`, the `≥ q^{m-3}` such points all carry `α₁`, and `θ_{m-2} < 2 q^{m-3}`.
* `obs2` (corrected AD21 Observation 2) and `graph` (AD21's application of Lemma 5.7) supply `W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.Q350.Half
open ProxGapTight ProxGapTight.Dev.Q350 Module

/-! ## Arithmetic -/

def th (Q d : ℕ) : ℕ := (Q ^ d - 1) / (Q - 1)

theorem th_dvd (Q d : ℕ) : (Q - 1) * th Q d = Q ^ d - 1 := by
  unfold th
  have : Q - 1 ∣ Q ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow Q 1 d
  exact Nat.mul_div_cancel' this

theorem th_succ (Q d : ℕ) (hQ : 2 ≤ Q) : th Q (d + 1) = Q ^ d + th Q d := by
  have h1 := th_dvd Q d
  have h2 := th_dvd Q (d + 1)
  have hP : 1 ≤ Q ^ d := Nat.one_le_pow _ _ (by omega)
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 2 := ⟨Q - 2, by omega⟩
  have e1 : Q' + 2 - 1 = Q' + 1 := by omega
  rw [e1] at h1 h2
  rw [pow_succ] at h2
  set P := (Q' + 2) ^ d
  have hr : (Q' + 1) * (P + th (Q' + 2) d) = (Q' + 1) * P + (P - 1) := by
    rw [Nat.mul_add, h1]
  have : (Q' + 1) * th (Q' + 2) (d + 1) = (Q' + 1) * (P + th (Q' + 2) d) := by
    rw [h2, hr]
    have : P * (Q' + 2) = (Q' + 1) * P + P := by ring
    omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

theorem th_mono (Q : ℕ) (hQ : 1 ≤ Q) {d d' : ℕ} (h : d ≤ d') : th Q d ≤ th Q d' := by
  unfold th
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right hQ h

theorem th_lt (Q d : ℕ) (hQ : 2 ≤ Q) : th Q d < Q ^ d := by
  have h1 := th_dvd Q d
  have hP : 1 ≤ Q ^ d := Nat.one_le_pow _ _ (by omega)
  have : th Q d ≤ (Q - 1) * th Q d := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-! ## Lines -/

section geo
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

theorem mem_linesOf (U : Submodule K (Fin m → K)) (ℓ : Lines K m) :
    ℓ ∈ linesOf U ↔ ℓ.1 ≤ U := by
  classical
  simp [linesOf]

theorem card_linesOf (U : Submodule K (Fin m → K)) :
    (linesOf U).card = th (Fintype.card K) (finrank K U) := by
  classical
  let f : Projectivization K U → Lines K m := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  haveI : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (linesOf U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_linesOf]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ (finrank K U) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), Nat.card_eq_fintype_card]
  rw [hc]
  rfl

/-- `Q = p^a` vanishes in `ZMod p` -/
theorem card_cast_zero (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) :
    ((Fintype.card K : ℕ) : ZMod p) = 0 := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hK] at h1
    simp at h1
  rw [hK]
  push_cast
  rw [ZMod.natCast_self, zero_pow ha]

theorem card_linesOf_cast (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a)
    (U : Submodule K (Fin m → K)) (hU : 1 ≤ finrank K U) :
    ((linesOf U).card : ZMod p) = 1 := by
  rw [card_linesOf U]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  unfold th
  rw [← Nat.geomSum_eq h2]
  push_cast
  rw [card_cast_zero p a hK]
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K U = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hU).symm⟩
  rw [hn, Finset.sum_range_succ']
  simp

theorem line_eq_of_le {ℓ ℓ' : Lines K m} (h : ℓ.1 ≤ ℓ'.1) : ℓ = ℓ' :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (by rw [ℓ.2, ℓ'.2]))

theorem finrank_line_inf {ℓ : Lines K m} {U : Submodule K (Fin m → K)} (h : ¬ ℓ.1 ≤ U) :
    finrank K ↥(ℓ.1 ⊓ U) = 0 := by
  have h1 : finrank K ↥(ℓ.1 ⊓ U) ≤ finrank K ℓ.1 := Submodule.finrank_mono inf_le_left
  rw [ℓ.2] at h1
  by_contra h0
  have e : finrank K ↥(ℓ.1 ⊓ U) = finrank K ℓ.1 := by rw [ℓ.2]; omega
  have e2 := Submodule.eq_of_le_of_finrank_eq inf_le_left e
  apply h
  rw [← e2]
  exact inf_le_right

theorem finrank_sup_line (U : Submodule K (Fin m → K)) (ℓ : Lines K m) (h : ¬ ℓ.1 ≤ U) :
    finrank K ↥(U ⊔ ℓ.1) = finrank K U + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U ℓ.1
  have h0 := finrank_line_inf h
  rw [inf_comm] at h0
  rw [h0, ℓ.2] at h1
  omega

/-! ## The projection -/

/-- the projection map `F^m → F^m / R ≃ F^(m-1)` -/
noncomputable def piR (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    (Fin m → K) →ₗ[K] (Fin (m - 1) → K) := e.toLinearMap ∘ₗ R.1.mkQ

/-- the plane `R + λ` -/
def P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : Submodule K (Fin m → K) :=
  (lam.1.comap e.toLinearMap).comap R.1.mkQ

theorem mem_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) (x : Fin m → K) : x ∈ P R e lam ↔ piR R e x ∈ lam.1 := Iff.rfl

theorem piR_eq_zero (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (x : Fin m → K) : piR R e x = 0 ↔ x ∈ R.1 := by
  simp [piR, Submodule.Quotient.mk_eq_zero]

theorem piR_surj (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    Function.Surjective (piR R e) := by
  intro y
  obtain ⟨q, rfl⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := R.1.mkQ_surjective q
  exact ⟨x, rfl⟩

theorem le_P_iff (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) (U : Submodule K (Fin m → K)) :
    U ≤ P R e lam ↔ U.map (piR R e) ≤ lam.1 := by
  rw [Submodule.map_le_iff_le_comap]
  rfl

theorem R_le_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : R.1 ≤ P R e lam := by
  intro x hx
  rw [mem_P, (piR_eq_zero R e x).mpr hx]
  exact lam.1.zero_mem

theorem finrank_map_line (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : Module.finrank K (ℓ.1.map (piR R e)) = 1 := by
  have h1 : Module.finrank K (ℓ.1.map (piR R e)) ≤ 1 := by
    have := Submodule.finrank_map_le (piR R e) ℓ.1
    rw [ℓ.2] at this
    exact this
  have h2 : ℓ.1.map (piR R e) ≠ ⊥ := by
    intro hb
    apply h
    apply line_eq_of_le
    intro x hx
    have hx' : piR R e x ∈ ℓ.1.map (piR R e) := Submodule.mem_map_of_mem hx
    rw [hb] at hx'
    exact (piR_eq_zero R e x).mp ((Submodule.mem_bot K).mp hx')
  have h3 : Module.finrank K (ℓ.1.map (piR R e)) ≠ 0 := by
    rwa [Ne, Submodule.finrank_eq_zero]
  omega

/-- the image line -/
noncomputable def lineMap (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : Lines K (m - 1) :=
  ⟨ℓ.1.map (piR R e), finrank_map_line R e ℓ h⟩

theorem le_P_iff_eq (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) (lam : Lines K (m - 1)) :
    ℓ.1 ≤ P R e lam ↔ lam = lineMap R e ℓ h := by
  rw [le_P_iff]
  constructor
  · intro hle
    exact (line_eq_of_le (ℓ := lineMap R e ℓ h) hle).symm
  · rintro rfl
    exact le_rfl

theorem proj_eq_sum {p : ℕ} (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (v : Lines K m → ZMod p)
    (lam : Lines K (m - 1)) :
    proj R e v lam = ∑ ℓ ∈ linesOf (P R e lam), v ℓ := by
  unfold proj P linesOf
  rfl

theorem finrank_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : finrank K (P R e lam) = 2 := by
  have hne : lam.1 ≠ ⊥ := by
    intro hb; have := lam.2; rw [hb, finrank_bot] at this; exact zero_ne_one this
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨w, hw⟩ := piR_surj R e v
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; exact hv0 hw.symm
  let ℓw : Lines K m := ⟨K ∙ w, finrank_span_singleton hw0⟩
  have hwR : w ∉ R.1 := by
    intro h; apply hv0; rw [← hw]; exact (piR_eq_zero R e w).mpr h
  have hnle : ¬ ℓw.1 ≤ R.1 := fun h => hwR (h (Submodule.mem_span_singleton_self w))
  have hlam : lam.1 = K ∙ v := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; simpa using hv
    · rw [finrank_span_singleton hv0, lam.2]
  have heq : P R e lam = R.1 ⊔ ℓw.1 := by
    apply le_antisymm
    · intro x hx
      rw [mem_P, hlam, Submodule.mem_span_singleton] at hx
      obtain ⟨a, ha⟩ := hx
      have h0 : piR R e (x - a • w) = 0 := by
        rw [map_sub, map_smul, hw, ha, sub_self]
      have hxR := (piR_eq_zero R e _).mp h0
      have : x = (x - a • w) + a • w := by abel
      rw [this]
      exact Submodule.add_mem_sup hxR
        (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w))
    · apply sup_le (R_le_P R e lam)
      rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      show piR R e x ∈ lam.1
      rw [hw]; exact hv
  rw [heq, finrank_sup_line R.1 ℓw hnle, R.2]

theorem card_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : (linesOf (P R e lam)).card = Fintype.card K + 1 := by
  rw [card_linesOf, finrank_P]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [th_succ _ 1 h2, pow_one]
  unfold th
  simp only [pow_one]
  rw [Nat.div_self (by omega)]

/-! ## Observation 1 / 3: tangent planes through `R` -/

theorem tangent {p : ℕ} (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (c : Lines K m → ZMod p) (hR : c R = 0) (lam : Lines K (m - 1)) (α : ZMod p) (hα : α ≠ 0)
    (hsum : ∑ ℓ ∈ linesOf (P R e lam), c ℓ = α)
    (hsec : (((linesOf (P R e lam)).filter (fun ℓ => c ℓ ≠ 0)).card ≤ 2 ∨
        Fintype.card K ≤ ((linesOf (P R e lam)).filter (fun ℓ => c ℓ ≠ 0)).card) ∧
      (((linesOf (P R e lam)).filter (fun ℓ => c ℓ ≠ 0)).card = Fintype.card K →
        ∑ ℓ ∈ linesOf (P R e lam), c ℓ = 0))
    (h2 : ((linesOf (P R e lam)).filter (fun ℓ => c ℓ ≠ 0)).card ≠ 2) :
    ∃ ℓ : Lines K m, ℓ.1 ≤ P R e lam ∧ c ℓ = α ∧
      ∀ ℓ' : Lines K m, ℓ'.1 ≤ P R e lam → c ℓ' ≠ 0 → ℓ' = ℓ := by
  classical
  set F := (linesOf (P R e lam)).filter (fun ℓ => c ℓ ≠ 0) with hF
  have hRmem : R ∈ linesOf (P R e lam) := (mem_linesOf _ _).mpr (R_le_P R e lam)
  have hle : F.card ≤ Fintype.card K := by
    have : F ⊆ (linesOf (P R e lam)).erase R := by
      intro ℓ hℓ
      rw [hF, Finset.mem_filter] at hℓ
      rw [Finset.mem_erase]
      exact ⟨fun h => hℓ.2 (h ▸ hR), hℓ.1⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hRmem, card_P] at this
    omega
  have hsumF : ∑ ℓ ∈ F, c ℓ = α := by
    rw [hF, Finset.sum_filter_ne_zero, hsum]
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rcases hsec.1 with h | h
  · interval_cases hc : F.card
    · rw [Finset.card_eq_zero] at hc
      rw [hc, Finset.sum_empty] at hsumF
      exact absurd hsumF.symm hα
    · obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hc
      rw [hℓ, Finset.sum_singleton] at hsumF
      have hmem : ℓ ∈ F := by rw [hℓ]; exact Finset.mem_singleton_self ℓ
      rw [hF, Finset.mem_filter, mem_linesOf] at hmem
      refine ⟨ℓ, hmem.1, hsumF, fun ℓ' h1 h2 => ?_⟩
      have : ℓ' ∈ F := by rw [hF, Finset.mem_filter, mem_linesOf]; exact ⟨h1, h2⟩
      rw [hℓ] at this
      exact Finset.mem_singleton.mp this
    · exact absurd rfl h2
  · have hq' : F.card = Fintype.card K := le_antisymm hle h
    have := hsec.2 hq'
    rw [hsum] at this
    exact absurd this hα

/-- `∑_λ incH κ λ = 1` -/
theorem sum_incH (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) {d : ℕ} (hd : 2 ≤ d)
    (κ : Hyp K d) : ∑ lam : Lines K d, incH (ZMod p) κ lam = 1 := by
  classical
  have : ∑ lam : Lines K d, incH (ZMod p) κ lam = ((linesOf κ.1).card : ZMod p) := by
    unfold incH linesOf
    rw [Finset.sum_boole]
  rw [this, card_linesOf_cast p a hK]
  have := κ.2; omega

end geo

/-! ## The count -/

theorem finish {p : ℕ} {K : Type} [Field K] [Fintype K] {m : ℕ} (hm : 4 ≤ m)
    (c : Lines K m → ZMod p) (R : Lines K m) (hR : c R = 0)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (κ : Hyp K (m - 1))
    (B : Submodule K (Fin (m - 1) → K)) (hBκ : B ≤ κ.1) (hBr : finrank K B + 3 ≤ m)
    (α : ZMod p) (hα : α ≠ 0)
    (hobs : ∀ lam : Lines K (m - 1), lam.1 ≤ κ.1 → ¬ lam.1 ≤ B →
      ∃ ℓ : Lines K m, ℓ.1 ≤ P R e lam ∧ c ℓ = α)
    (W : Codim2 K m)
    (hW : ∀ ℓ : Lines K m, ℓ.1 ≤ κ.1.comap (piR R e) → ¬ ℓ.1 ≤ B.comap (piR R e) →
      c ℓ ≠ 0 → ℓ.1 ≤ W.1) :
    (linesOf W.1).card < 2 * ((linesOf W.1).filter (fun ℓ => c ℓ = α)).card := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨n, hn⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  let D := linesOf κ.1 \ linesOf B
  have hκr : finrank K κ.1 = n + 1 := by have := κ.2; omega
  have hWr : finrank K W.1 = n + 1 := by have := W.2; omega
  have hD : (Fintype.card K) ^ n ≤ D.card := by
    have hsub : linesOf B ⊆ linesOf κ.1 := by
      intro ℓ; rw [mem_linesOf, mem_linesOf]; exact fun h => h.trans hBκ
    rw [Finset.card_sdiff_of_subset hsub, card_linesOf, card_linesOf, hκr, th_succ _ n hq]
    have := th_mono (Fintype.card K) (by omega) (show finrank K B ≤ n by omega)
    omega
  have key : ∀ lam ∈ D, ∃ ℓ : Lines K m, ℓ.1 ≤ P R e lam ∧ c ℓ = α := by
    intro lam hlam
    simp only [D, Finset.mem_sdiff, mem_linesOf] at hlam
    exact hobs lam hlam.1 hlam.2
  haveI : Nonempty (Lines K m) := ⟨R⟩
  choose! g hg using key
  have hgR : ∀ lam ∈ D, g lam ≠ R := fun lam h he => hα ((hg lam h).2 ▸ he ▸ hR)
  have hmaps : ∀ lam ∈ D, g lam ∈ (linesOf W.1).filter (fun ℓ => c ℓ = α) := by
    intro lam hlam
    have hl := hlam
    simp only [D, Finset.mem_sdiff, mem_linesOf] at hl
    have hne := hgR lam hlam
    have heq := (le_P_iff_eq R e (g lam) hne lam).mp (hg lam hlam).1
    have hmap : (g lam).1.map (piR R e) = lam.1 := (congrArg Subtype.val heq).symm
    rw [Finset.mem_filter, mem_linesOf]
    refine ⟨hW _ ?_ ?_ ?_, (hg lam hlam).2⟩
    · rw [← Submodule.map_le_iff_le_comap, hmap]; exact hl.1
    · rw [← Submodule.map_le_iff_le_comap, hmap]; exact hl.2
    · rw [(hg lam hlam).2]; exact hα
  have hinj : Set.InjOn g D := by
    intro l1 h1 l2 h2 he
    have a1 := (le_P_iff_eq R e (g l1) (hgR l1 h1) l1).mp (hg l1 h1).1
    have a2 := (le_P_iff_eq R e (g l1) (hgR l1 h1) l2).mp (he ▸ (hg l2 h2).1)
    rw [a1, a2]
  have hcard := Finset.card_le_card_of_injOn g (fun lam h => hmaps lam h) hinj
  rw [card_linesOf, hWr, th_succ _ n hq]
  have := th_lt (Fintype.card K) n hq
  omega

/-! ## Copied from Q350Hyp (Lemma 5.7 for subspaces) -/

theorem th_one (Q : ℕ) (hQ : 2 ≤ Q) : th Q 1 = 1 := by
  unfold th; simp only [pow_one]; exact Nat.div_self (by omega)

theorem th_two (Q : ℕ) (hQ : 2 ≤ Q) : th Q 2 = Q + 1 := by
  rw [th_succ Q 1 hQ, th_one Q hQ, pow_one]

/-- `2((q-1)q^n + 1) > θ_{n+2}` for `q ≥ 4` -/
theorem arith (q n : ℕ) (hq : 4 ≤ q) : th q (n + 2) < 2 * ((q - 1) * q ^ n + 1) := by
  have h := th_dvd q (n + 2)
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 4 := ⟨q - 4, by omega⟩
  have e1 : r + 4 - 1 = r + 3 := by omega
  rw [e1] at h ⊢
  have hQ : 1 ≤ (r + 4) ^ n := Nat.one_le_pow _ _ (by omega)
  have e2 : (r + 4) ^ (n + 2) = (r + 4) ^ n * (r + 4) ^ 2 := by ring
  rw [e2] at h
  set Q := (r + 4) ^ n
  by_contra hcon
  push Not at hcon
  have h3 : (r + 3) * (2 * ((r + 3) * Q + 1)) ≤ (r + 3) * th (r + 4) (n + 2) :=
    Nat.mul_le_mul_left _ hcon
  have h4 : 1 ≤ Q * (r + 4) ^ 2 := by nlinarith
  have h5 : (r + 3) * th (r + 4) (n + 2) + 1 = Q * (r + 4) ^ 2 := by omega
  nlinarith

/-! ## Lines and subspaces -/


section geoH
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

theorem finrank_join {P X : Lines K m} (h : P ≠ X) : finrank K ↥(P.1 ⊔ X.1) = 2 := by
  have hX : ¬ X.1 ≤ P.1 := fun hle => h (line_eq_of_le hle).symm
  rw [finrank_sup_line P.1 X hX, P.2]

/-- a point `ℓ ≠ P` on the line `P X` spans it with `P` -/
theorem join_eq {P X ℓ : Lines K m} (hPX : P ≠ X) (hℓ : ℓ.1 ≤ P.1 ⊔ X.1) (hℓP : ℓ ≠ P) :
    P.1 ⊔ ℓ.1 = P.1 ⊔ X.1 :=
  Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_left hℓ)
    (by rw [finrank_join hPX, finrank_join (Ne.symm hℓP)])

/-- the line `P X` meets `π` only in `X` when `X ∈ π ∌ P` -/
theorem join_inf {P X Y : Lines K m} {π : Submodule K (Fin m → K)} (hX : X.1 ≤ π)
    (hP : ¬ P.1 ≤ π) (hY : Y.1 ≤ π) (hYl : Y.1 ≤ P.1 ⊔ X.1) : Y = X := by
  by_contra hne
  have hPX : P ≠ X := fun e => hP (e ▸ hX)
  have e := Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_right hYl :
      X.1 ⊔ Y.1 ≤ P.1 ⊔ X.1)
    (by rw [finrank_join hPX, finrank_join (Ne.symm hne)])
  apply hP
  calc P.1 ≤ P.1 ⊔ X.1 := le_sup_left
    _ = X.1 ⊔ Y.1 := e.symm
    _ ≤ π := sup_le hX hY

theorem exists_sub (V : Submodule K (Fin m → K)) (k : ℕ) (hk : k ≤ finrank K V) :
    ∃ W ≤ V, finrank K W = k := by
  let b := Module.finBasis K V
  let f : Fin k → (Fin m → K) := fun i => (b (Fin.castLE hk i) : Fin m → K)
  have hli : LinearIndependent K f := by
    have := b.linearIndependent.comp _ (Fin.castLE_injective hk)
    exact this.map' V.subtype (Submodule.ker_subtype V)
  refine ⟨Submodule.span K (Set.range f), ?_, ?_⟩
  · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (b _).2
  · rw [finrank_span_eq_card hli, Fintype.card_fin]

/-! ## The counting step -/

theorem count_lower (A : Lines K m → Prop) [DecidablePred A]
    (hA : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
      2 ≤ ((linesOf s).filter A).card → Fintype.card K ≤ ((linesOf s).filter A).card)
    (V π H : Submodule K (Fin m → K)) (n : ℕ) (hπ : π ≤ V) (hπr : finrank K π = n + 1)
    (hH : H ≤ π) (hHr : finrank K H = n)
    (hAπ : ∀ ℓ : Lines K m, ℓ.1 ≤ π → ¬ ℓ.1 ≤ H → A ℓ)
    (P : Lines K m) (hP : A P) (hPV : P.1 ≤ V) (hPπ : ¬ P.1 ≤ π) :
    (Fintype.card K - 1) * Fintype.card K ^ n + 1 ≤ ((linesOf V).filter A).card := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  set q := Fintype.card K with hqd
  let D := linesOf π \ linesOf H
  have hD : D.card = q ^ n := by
    have hsub : linesOf H ⊆ linesOf π := by
      intro ℓ; rw [mem_linesOf, mem_linesOf]; exact fun h => h.trans hH
    rw [Finset.card_sdiff_of_subset hsub, card_linesOf, card_linesOf, hπr, hHr,
      th_succ q n hq]
    simp only [← hqd]
    omega
  let F : Lines K m → Finset (Lines K m) := fun X => ((linesOf (P.1 ⊔ X.1)).filter A).erase P
  have hmemD : ∀ X ∈ D, X.1 ≤ π ∧ ¬ X.1 ≤ H := by
    intro X hX
    simp only [D, Finset.mem_sdiff, mem_linesOf] at hX
    exact hX
  have hF : ∀ X ∈ D, q - 1 ≤ (F X).card := by
    intro X hX
    obtain ⟨hXπ, hXH⟩ := hmemD X hX
    have hPX : P ≠ X := fun e => hPπ (e ▸ hXπ)
    have h2 : 2 ≤ ((linesOf (P.1 ⊔ X.1)).filter A).card := by
      have : ({P, X} : Finset (Lines K m)) ⊆ (linesOf (P.1 ⊔ X.1)).filter A := by
        intro ℓ hℓ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
        rw [Finset.mem_filter, mem_linesOf]
        rcases hℓ with rfl | rfl
        · exact ⟨le_sup_left, hP⟩
        · exact ⟨le_sup_right, hAπ _ hXπ hXH⟩
      have := Finset.card_le_card this
      rwa [Finset.card_pair hPX] at this
    have hq' := hA _ (finrank_join hPX) h2
    have hmem : P ∈ (linesOf (P.1 ⊔ X.1)).filter A := by
      rw [Finset.mem_filter, mem_linesOf]; exact ⟨le_sup_left, hP⟩
    rw [Finset.card_erase_of_mem hmem]
    omega
  have hdisj : ∀ X ∈ D, ∀ Y ∈ D, X ≠ Y → Disjoint (F X) (F Y) := by
    intro X hX Y hY hXY
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    simp only [F, Finset.mem_erase, Finset.mem_filter, mem_linesOf] at h1 h2
    have hXπ := (hmemD X hX).1
    have hYπ := (hmemD Y hY).1
    have hPX : P ≠ X := fun e => hPπ (e ▸ hXπ)
    have hPY : P ≠ Y := fun e => hPπ (e ▸ hYπ)
    have e1 := join_eq hPX h1.2.1 h1.1
    have e2 := join_eq hPY h2.2.1 h2.1
    have hYle : Y.1 ≤ P.1 ⊔ X.1 := by rw [← e1, e2]; exact le_sup_right
    exact hXY (join_inf hXπ hPπ hYπ hYle).symm
  have hU : (q - 1) * q ^ n ≤ (D.biUnion F).card := by
    rw [Finset.card_biUnion hdisj]
    have := Finset.card_nsmul_le_sum D (fun X => (F X).card) (q - 1) hF
    rw [smul_eq_mul, hD] at this
    linarith
  have hPU : P ∉ D.biUnion F := by
    simp [F]
  have hsub : insert P (D.biUnion F) ⊆ (linesOf V).filter A := by
    intro ℓ hℓ
    rw [Finset.mem_insert] at hℓ
    rw [Finset.mem_filter, mem_linesOf]
    rcases hℓ with rfl | hℓ
    · exact ⟨hPV, hP⟩
    · rw [Finset.mem_biUnion] at hℓ
      obtain ⟨X, hX, hℓX⟩ := hℓ
      simp only [F, Finset.mem_erase, Finset.mem_filter, mem_linesOf] at hℓX
      exact ⟨hℓX.2.1.trans (sup_le hPV ((hmemD X hX).1.trans hπ)), hℓX.2.2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hPU] at this
  omega

/-- the inductive step, for one of `A`, `Aᶜ` -/
theorem main_count (A : Lines K m → Prop) [DecidablePred A]
    (hA : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
      2 ≤ ((linesOf s).filter A).card → Fintype.card K ≤ ((linesOf s).filter A).card)
    (n : ℕ) (V : Submodule K (Fin m → K)) (hV : finrank K V = n + 2)
    (IH : ∀ π : Submodule K (Fin m → K), π ≤ V → finrank K π = n + 1 →
      ∃ H ≤ π, finrank K H + 1 = finrank K π ∧
        ((∀ ℓ : Lines K m, ℓ.1 ≤ π → A ℓ → ℓ.1 ≤ H) ∨
          (∀ ℓ : Lines K m, ℓ.1 ≤ π → ¬ A ℓ → ℓ.1 ≤ H)))
    (hnot : ∀ π : Submodule K (Fin m → K), π ≤ V → finrank K π = n + 1 →
      ∃ ℓ : Lines K m, ℓ.1 ≤ V ∧ A ℓ ∧ ¬ ℓ.1 ≤ π) :
    (Fintype.card K - 1) * Fintype.card K ^ n + 1 ≤ ((linesOf V).filter A).card := by
  classical
  haveI : Finite (Submodule K (Fin m → K)) :=
    Finite.of_injective (fun p : Submodule K (Fin m → K) => (p : Set (Fin m → K)))
      SetLike.coe_injective
  let S : Set (Submodule K (Fin m → K)) := {π | π ≤ V ∧ finrank K π = n + 1}
  let T := (Set.toFinite S).toFinset
  obtain ⟨π0, hπ0V, hπ0r⟩ := exists_sub V (n + 1) (by omega)
  have hTne : T.Nonempty := ⟨π0, by simp [T, S, hπ0V, hπ0r]⟩
  obtain ⟨π, hπT, hmax⟩ := Finset.exists_max_image T (fun π => ((linesOf π).filter A).card) hTne
  simp only [T, S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hπT hmax
  obtain ⟨hπV, hπr⟩ := hπT
  obtain ⟨H, hHπ, hHr, hcase⟩ := IH π hπV hπr
  obtain ⟨X, hXV, hXA, hXπ⟩ := hnot π hπV hπr
  rcases hcase with hc | hc
  · exfalso
    have hXH : ¬ X.1 ≤ H := fun h => hXπ (h.trans hHπ)
    have hr : finrank K ↥(H ⊔ X.1) = n + 1 := by rw [finrank_sup_line H X hXH]; omega
    have hle := hmax (H ⊔ X.1) ⟨sup_le (hHπ.trans hπV) hXV, hr⟩
    have hss : (linesOf π).filter A ⊂ (linesOf (H ⊔ X.1)).filter A := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨X, ?_, ?_⟩
        · rw [Finset.mem_filter, mem_linesOf]; exact ⟨le_sup_right, hXA⟩
        · rw [Finset.mem_filter, mem_linesOf]; exact fun h => hXπ h.1
      · intro ℓ hℓ
        rw [Finset.mem_filter, mem_linesOf] at hℓ ⊢
        exact ⟨(hc ℓ hℓ.1 hℓ.2).trans le_sup_left, hℓ.2⟩
    have := Finset.card_lt_card hss
    omega
  · refine count_lower A hA V π H n hπV hπr hHπ (by omega) ?_ X hXA hXV hXπ
    intro ℓ hℓπ hℓH
    by_contra hn
    exact hℓH (hc ℓ hℓπ hn)

theorem gen (hq : 4 ≤ Fintype.card K) (n : ℕ) :
    ∀ (A : Lines K m → Prop) [DecidablePred A],
      (∀ s : Submodule K (Fin m → K), finrank K s = 2 →
        ((linesOf s).filter A).card ≤ 1 ∨ Fintype.card K ≤ ((linesOf s).filter A).card) →
      ∀ V : Submodule K (Fin m → K), finrank K V = n + 1 →
        ∃ H ≤ V, finrank K H + 1 = finrank K V ∧
          ((∀ ℓ : Lines K m, ℓ.1 ≤ V → A ℓ → ℓ.1 ≤ H) ∨
            (∀ ℓ : Lines K m, ℓ.1 ≤ V → ¬ A ℓ → ℓ.1 ≤ H)) := by
  induction n with
  | zero =>
    intro A _ _ V hV
    refine ⟨⊥, bot_le, by rw [finrank_bot, hV], ?_⟩
    by_cases hex : ∃ ℓ : Lines K m, ℓ.1 ≤ V ∧ A ℓ
    · obtain ⟨ℓ, hℓV, hℓA⟩ := hex
      right
      intro ℓ' hℓ'V hℓ'A
      exfalso
      have e1 := Submodule.eq_of_le_of_finrank_eq hℓV (by rw [ℓ.2, hV])
      have e2 := Submodule.eq_of_le_of_finrank_eq hℓ'V (by rw [ℓ'.2, hV])
      have : ℓ' = ℓ := Subtype.ext (e2.trans e1.symm)
      exact hℓ'A (this ▸ hℓA)
    · left
      intro ℓ hℓV hℓA
      exact absurd ⟨ℓ, hℓV, hℓA⟩ hex
  | succ n ih =>
    intro A _ hA V hV
    classical
    have hq2 : 2 ≤ Fintype.card K := by omega
    by_contra hcon
    push Not at hcon
    -- `hcon : ∀ H ≤ V, finrank H + 1 = finrank V → (∃ ...) ∧ (∃ ...)`
    have hA1 : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
        2 ≤ ((linesOf s).filter A).card → Fintype.card K ≤ ((linesOf s).filter A).card := by
      intro s hs h2
      rcases hA s hs with h | h
      · omega
      · exact h
    have hA2 : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
        2 ≤ ((linesOf s).filter (fun ℓ => ¬ A ℓ)).card →
          Fintype.card K ≤ ((linesOf s).filter (fun ℓ => ¬ A ℓ)).card := by
      intro s hs h2
      have htot := Finset.card_filter_add_card_filter_not (s := linesOf s) A
      rw [card_linesOf, hs, th_two _ hq2] at htot
      rcases hA s hs with h | h
      · omega
      · omega
    have c1 := main_count A hA1 n V hV
      (fun π hπ hπr => ih A hA π hπr)
      (fun π hπ hπr => by
        obtain ⟨⟨ℓ, h1, h2, h3⟩, _⟩ := hcon π hπ (by omega)
        exact ⟨ℓ, h1, h2, h3⟩)
    have c2 := main_count (fun ℓ => ¬ A ℓ) hA2 n V hV
      (fun π hπ hπr => by
        obtain ⟨H, h1, h2, h3⟩ := ih A hA π hπr
        refine ⟨H, h1, h2, ?_⟩
        rcases h3 with h | h
        · right; intro ℓ hℓ hn; exact h ℓ hℓ (not_not.mp hn)
        · left; exact h)
      (fun π hπ hπr => by
        obtain ⟨_, ⟨ℓ, h1, h2, h3⟩⟩ := hcon π hπ (by omega)
        exact ⟨ℓ, h1, h2, h3⟩)
    have htot := Finset.card_filter_add_card_filter_not (s := linesOf V) A
    rw [card_linesOf, hV, show n + 1 + 1 = n + 2 from rfl] at htot
    have := arith (Fintype.card K) n hq
    omega


end geoH

section geoX
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

theorem finrank_comap_piR (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (U : Submodule K (Fin (m - 1) → K)) :
    finrank K (U.comap (piR R e)) = finrank K U + 1 := by
  have hRU : R.1 ≤ U.comap (piR R e) := by
    intro x hx
    rw [Submodule.mem_comap, (piR_eq_zero R e x).mpr hx]; exact U.zero_mem
  have h := LinearMap.finrank_range_add_finrank_ker
    ((piR R e).domRestrict (U.comap (piR R e)))
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq_of_surjective (piR_surj R e),
    LinearMap.ker_domRestrict] at h
  have hk : LinearMap.ker (piR R e) = R.1 := by
    ext x; rw [LinearMap.mem_ker, piR_eq_zero]
  rw [hk, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hRU), R.2] at h
  omega

open Classical in
theorem card_filter_le_one (s U : Submodule K (Fin m → K)) (hs : finrank K s = 2)
    (hsU : ¬ s ≤ U) : ((linesOf s).filter (fun ℓ => ℓ.1 ≤ U)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  simp only [Finset.mem_filter, mem_linesOf] at ha hb
  apply hsU
  have : a.1 ⊔ b.1 = s :=
    Submodule.eq_of_le_of_finrank_eq (sup_le ha.1 hb.1) (by rw [finrank_join hab, hs])
  rw [← this]; exact sup_le ha.2 hb.2

end geoX

/-! ## The geometric core (AD21 Observation 2 / 4 and Lemma 5.7 inside `λ₁`) -/

/-! ## Material for Observation 2 -/

section obs2geo
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

theorem le_comap_iff (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (X : Lines K m) (h : X ≠ R) (U : Submodule K (Fin (m - 1) → K)) :
    X.1 ≤ U.comap (piR R e) ↔ (lineMap R e X h).1 ≤ U := by
  rw [← Submodule.map_le_iff_le_comap]; rfl

theorem R_le_comap (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (U : Submodule K (Fin (m - 1) → K)) : R.1 ≤ U.comap (piR R e) := by
  intro x hx
  show piR R e x ∈ U
  rw [(piR_eq_zero R e x).mpr hx]
  exact zero_mem _

theorem exists_e (R : Lines K m) :
    Nonempty (((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) := by
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  have := Submodule.finrank_quotient_add_finrank R.1
  rw [R.2, Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun]; omega

theorem plane_eq (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (X : Lines K m) (h : X ≠ R) : P R e (lineMap R e X h) = R.1 ⊔ X.1 :=
  (Submodule.eq_of_le_of_finrank_eq (sup_le (R_le_P R e _) ((le_P_iff_eq R e X h _).mpr rfl))
    (by rw [finrank_join (Ne.symm h), finrank_P])).symm

theorem ker_piR (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    LinearMap.ker (piR R e) = R.1 := by
  ext x; rw [LinearMap.mem_ker, piR_eq_zero]

theorem comap_map_piR (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (W : Submodule K (Fin m → K)) (hW : R.1 ≤ W) : (W.map (piR R e)).comap (piR R e) = W :=
  Submodule.comap_map_eq_self (by rw [ker_piR]; exact hW)

theorem P_eq_comap (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : P R e lam = lam.1.comap (piR R e) := rfl

theorem map_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : (P R e lam).map (piR R e) = lam.1 :=
  Submodule.map_comap_eq_of_surjective (piR_surj R e) _

theorem finrank_map_piR (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (W : Submodule K (Fin m → K)) (hW : R.1 ≤ W) :
    finrank K (W.map (piR R e)) + 1 = finrank K W := by
  have := finrank_comap_piR R e (W.map (piR R e))
  rw [comap_map_piR R e W hW] at this
  omega

theorem finrank_comap_hyp (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (κ : Hyp K (m - 1)) :
    finrank K (κ.1.comap (piR R e)) = m - 1 := by
  have := finrank_comap_piR R e κ.1
  have := κ.2
  omega

theorem exists_point (W : Submodule K (Fin m → K)) (hW : 1 ≤ finrank K W) :
    ∃ ℓ : Lines K m, ℓ.1 ≤ W := by
  have hne : W ≠ ⊥ := by intro h; rw [h, finrank_bot] at hW; omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨⟨K ∙ v, finrank_span_singleton hv0⟩, by rw [Submodule.span_le]; simpa using hv⟩

theorem meet_exists (σ A B : Submodule K (Fin m → K)) (hσ : finrank K σ = 3)
    (hA : finrank K A = 2) (hB : finrank K B = 2) (hAσ : A ≤ σ) (hBσ : B ≤ σ) :
    ∃ ℓ : Lines K m, ℓ.1 ≤ A ∧ ℓ.1 ≤ B := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h2 : finrank K ↥(A ⊔ B) ≤ 3 := hσ ▸ Submodule.finrank_mono (sup_le hAσ hBσ)
  obtain ⟨ℓ, hℓ⟩ := exists_point (A ⊓ B) (by omega)
  exact ⟨ℓ, hℓ.trans inf_le_left, hℓ.trans inf_le_right⟩

theorem two_pts {A : Submodule K (Fin m → K)} (hA : finrank K A = 2) {Z1 Z2 : Lines K m}
    (h : Z1 ≠ Z2) (h1 : Z1.1 ≤ A) (h2 : Z2.1 ≤ A) : Z1.1 ⊔ Z2.1 = A :=
  Submodule.eq_of_le_of_finrank_eq (sup_le h1 h2) (by rw [finrank_join h, hA])

theorem hyp_inf_rank {d : ℕ} (κ κ' : Hyp K d) (hne : κ ≠ κ') :
    finrank K ↥(κ.1 ⊓ κ'.1) + 1 = finrank K κ.1 := by
  have hκ1 := κ.2
  have hκ2 := κ'.2
  have hlt : κ.1 < κ.1 ⊔ κ'.1 := by
    refine lt_of_le_of_ne le_sup_left fun heq => hne ?_
    have hle : κ'.1 ≤ κ.1 := by rw [heq]; exact le_sup_right
    exact (Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by omega))).symm
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : finrank K ↥(κ.1 ⊔ κ'.1) ≤ d := by
    have := Submodule.finrank_le (κ.1 ⊔ κ'.1)
    rwa [Module.finrank_fin_fun] at this
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq κ.1 κ'.1
  omega

theorem hyp2_inf (L1 L3 : Submodule K (Fin m → K)) (h1 : finrank K L1 = m - 1)
    (h3 : finrank K L3 = m - 1) (hne : L3 ≠ L1) (hm : 1 ≤ m) :
    finrank K ↥(L1 ⊓ L3) = m - 2 := by
  have hlt : L1 < L1 ⊔ L3 := by
    refine lt_of_le_of_ne le_sup_left fun heq => hne ?_
    have hle : L3 ≤ L1 := by rw [heq]; exact le_sup_right
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have a := Submodule.finrank_lt_finrank_of_lt hlt
  have b : finrank K ↥(L1 ⊔ L3) ≤ m := by
    have := Submodule.finrank_le (L1 ⊔ L3); rwa [Module.finrank_fin_fun] at this
  have c := Submodule.finrank_sup_add_finrank_inf_eq L1 L3
  omega

/-- the secant property (AD21 Lemma 5.6) as a hypothesis, with `σc = c · 1` -/
def SecH {p : ℕ} (c : Lines K m → ZMod p) (σc : ZMod p) : Prop :=
  ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
    (((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≤ 2 ∨
        Fintype.card K ≤ ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card) ∧
      (((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card = 2 → ∑ ℓ ∈ linesOf s, c ℓ = σc) ∧
      (((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card = Fintype.card K →
        ∑ ℓ ∈ linesOf s, c ℓ = 0)

/-- a line through a non-support point whose sum is neither `0` nor `c · 1` is a tangent -/
theorem tanM {p : ℕ} (c : Lines K m → ZMod p) (σc : ZMod p) (hsec : SecH c σc)
    (M : Submodule K (Fin m → K)) (hM : finrank K M = 2) (Z0 : Lines K m) (hZ0 : Z0.1 ≤ M)
    (hc0 : c Z0 = 0) (β : ZMod p) (hβ : β ≠ 0) (hβσ : β ≠ σc)
    (hsum : ∑ ℓ ∈ linesOf M, c ℓ = β) :
    ∃ Z : Lines K m, Z.1 ≤ M ∧ c Z = β ∧
      ∀ Z' : Lines K m, Z'.1 ≤ M → c Z' ≠ 0 → Z' = Z := by
  classical
  obtain ⟨h1, h2, h3⟩ := hsec M hM
  set F := (linesOf M).filter (fun ℓ => c ℓ ≠ 0) with hF
  have hZmem : Z0 ∈ linesOf M := (mem_linesOf _ _).mpr hZ0
  have hle : F.card ≤ Fintype.card K := by
    have : F ⊆ (linesOf M).erase Z0 := by
      intro ℓ hℓ
      rw [hF, Finset.mem_filter] at hℓ
      rw [Finset.mem_erase]
      exact ⟨fun h => hℓ.2 (h ▸ hc0), hℓ.1⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hZmem, card_linesOf, hM, th_two _ Fintype.one_lt_card] at this
    omega
  have hsumF : ∑ ℓ ∈ F, c ℓ = β := by rw [hF, Finset.sum_filter_ne_zero, hsum]
  rcases h1 with h | h
  · interval_cases hc : F.card
    · rw [Finset.card_eq_zero] at hc
      rw [hc, Finset.sum_empty] at hsumF
      exact absurd hsumF.symm hβ
    · obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hc
      rw [hℓ, Finset.sum_singleton] at hsumF
      have hmem : ℓ ∈ F := by rw [hℓ]; exact Finset.mem_singleton_self ℓ
      rw [hF, Finset.mem_filter, mem_linesOf] at hmem
      refine ⟨ℓ, hmem.1, hsumF, fun ℓ' h1 h2 => ?_⟩
      have : ℓ' ∈ F := by rw [hF, Finset.mem_filter, mem_linesOf]; exact ⟨h1, h2⟩
      rw [hℓ] at this
      exact Finset.mem_singleton.mp this
    · exact absurd (hsum.symm.trans (h2 rfl)) hβσ
  · have := h3 (le_antisymm hle h)
    rw [hsum] at this
    exact absurd this hβ

theorem card_one_of {p : ℕ} (c : Lines K m → ZMod p) (M : Submodule K (Fin m → K))
    (Z : Lines K m) (hZ : Z.1 ≤ M) (hcZ : c Z ≠ 0)
    (hu : ∀ Z' : Lines K m, Z'.1 ≤ M → c Z' ≠ 0 → Z' = Z) :
    ((linesOf M).filter (fun ℓ => c ℓ ≠ 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨Z, ?_⟩
  ext ℓ
  simp only [Finset.mem_filter, mem_linesOf, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩; exact hu ℓ h1 h2
  · rintro rfl; exact ⟨hZ, hcZ⟩

theorem le_one_of (S : Lines K m → Prop) [DecidablePred S] (M : Submodule K (Fin m → K))
    (h : ((linesOf M).filter S).card = 1) (Z Z' : Lines K m) (h1 : Z.1 ≤ M) (h2 : Z'.1 ≤ M)
    (h3 : S Z) (h4 : S Z') : Z = Z' :=
  Finset.card_le_one.mp h.le Z (by rw [Finset.mem_filter, mem_linesOf]; exact ⟨h1, h3⟩) Z'
    (by rw [Finset.mem_filter, mem_linesOf]; exact ⟨h2, h4⟩)

/-- counting the points of a plane `σ` through the lines through one of its points `C` -/
theorem fiber_count (C : Lines K m) (σ M0 : Submodule K (Fin m → K)) (hσ : finrank K σ = 3)
    (hCσ : C.1 ≤ σ) (hM0 : finrank K M0 = 2) (hCM0 : C.1 ≤ M0) (hM0σ : M0 ≤ σ)
    (S : Lines K m → Prop) [DecidablePred S] (hSC : ¬ S C)
    (h1 : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → C.1 ≤ M → M ≤ σ → M ≠ M0 →
      ((linesOf M).filter S).card = 1) :
    ((linesOf σ).filter S).card = ((linesOf M0).filter S).card + Fintype.card K := by
  classical
  obtain ⟨e⟩ := exists_e C
  have hlbr : finrank K (σ.map (piR C e)) = 2 := by
    have := finrank_map_piR C e σ hCσ; omega
  let F : Lines K (m - 1) → Finset (Lines K m) := fun lam => (linesOf (P C e lam)).filter S
  have hU : (linesOf σ).filter S = (linesOf (σ.map (piR C e))).biUnion F := by
    ext ℓ
    simp only [Finset.mem_filter, mem_linesOf, Finset.mem_biUnion, F]
    constructor
    · rintro ⟨h1, h2⟩
      have hne : ℓ ≠ C := fun h => hSC (h ▸ h2)
      exact ⟨lineMap C e ℓ hne, Submodule.map_mono h1, (le_P_iff C e _ ℓ.1).mpr le_rfl, h2⟩
    · rintro ⟨lam, hlam, h1, h2⟩
      refine ⟨?_, h2⟩
      calc ℓ.1 ≤ P C e lam := h1
        _ = lam.1.comap (piR C e) := P_eq_comap C e lam
        _ ≤ (σ.map (piR C e)).comap (piR C e) := Submodule.comap_mono hlam
        _ = σ := comap_map_piR C e σ hCσ
  have hdisj : ((linesOf (σ.map (piR C e)) : Set (Lines K (m - 1)))).PairwiseDisjoint F := by
    intro μ _ μ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ℓ h1 h2
    simp only [F, Finset.mem_filter, mem_linesOf] at h1 h2
    have hb : ℓ ≠ C := fun h => hSC (h ▸ h1.2)
    exact hne (((le_P_iff_eq C e ℓ hb μ).mp h1.1).trans ((le_P_iff_eq C e ℓ hb μ').mp h2.1).symm)
  rw [hU, Finset.card_biUnion hdisj]
  let lam0 : Lines K (m - 1) :=
    ⟨M0.map (piR C e), by have := finrank_map_piR C e M0 hCM0; omega⟩
  have hlam0 : lam0 ∈ linesOf (σ.map (piR C e)) := (mem_linesOf _ _).mpr (Submodule.map_mono hM0σ)
  have hP0 : P C e lam0 = M0 := comap_map_piR C e M0 hCM0
  rw [← Finset.add_sum_erase _ _ hlam0]
  have hrest : ∀ lam ∈ (linesOf (σ.map (piR C e))).erase lam0, (F lam).card = 1 := by
    intro lam hlam
    rw [Finset.mem_erase, mem_linesOf] at hlam
    apply h1 (P C e lam) (finrank_P C e lam) (R_le_P C e lam)
    · rw [P_eq_comap]
      calc lam.1.comap (piR C e) ≤ (σ.map (piR C e)).comap (piR C e) :=
            Submodule.comap_mono hlam.2
        _ = σ := comap_map_piR C e σ hCσ
    · intro heq
      apply hlam.1
      apply Subtype.ext
      rw [← map_P C e lam, heq]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_erase_of_mem hlam0, card_linesOf, hlbr, th_two _ Fintype.one_lt_card]
  have : (F lam0).card = ((linesOf M0).filter S).card := by simp only [F, hP0]
  omega

theorem card_add_three {α : Type} [DecidableEq α] (A U : Finset α) (a b d : α) (hA : A ⊆ U)
    (ha : a ∈ U) (hb : b ∈ U) (hd : d ∈ U) (ha' : a ∉ A) (hb' : b ∉ A) (hd' : d ∉ A)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) : A.card + 3 ≤ U.card := by
  have hsub : insert a (insert b (insert d A)) ⊆ U := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact ha
    · exact hb
    · exact hd
    · exact hA hx
  have := Finset.card_le_card hsub
  have h2 : b ∉ insert d A := by simp [hbd, hb']
  have h3 : a ∉ insert b (insert d A) := by simp [hab, had, ha']
  rw [Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem hd'] at this
  omega

theorem exists_D (S : Lines K m → Prop) [DecidablePred S] (t0 L : Submodule K (Fin m → K))
    (ht : finrank K t0 = 2) (hL : finrank K L = 2) (htS : ((linesOf t0).filter S).card = 2)
    (hLt : L ≠ t0) : ∃ D : Lines K m, D.1 ≤ t0 ∧ S D ∧ ¬ D.1 ≤ L := by
  classical
  obtain ⟨D1, D2, hD12, hDt⟩ := Finset.card_eq_two.mp htS
  have hD1 : D1 ∈ (linesOf t0).filter S := by rw [hDt]; simp
  have hD2 : D2 ∈ (linesOf t0).filter S := by rw [hDt]; simp
  rw [Finset.mem_filter, mem_linesOf] at hD1 hD2
  by_cases h1 : D1.1 ≤ L
  · by_cases h2 : D2.1 ≤ L
    · exact absurd ((two_pts hL hD12 h1 h2).symm.trans (two_pts ht hD12 hD1.1 hD2.1)) hLt
    · exact ⟨D2, hD2.1, hD2.2, h2⟩
  · exact ⟨D1, hD1.1, hD1.2, h1⟩

/-- the U-configuration, second half: a `≥ q`-secant `L` through `X` -/
theorem u_config_L (hq : 4 ≤ Fintype.card K) (S : Lines K m → Prop) [DecidablePred S]
    (σ0 s t0 L : Submodule K (Fin m → K)) (hσ : finrank K σ0 = 3)
    (hs : finrank K s = 2) (ht : finrank K t0 = 2) (hL : finrank K L = 2)
    (hsσ : s ≤ σ0) (htσ : t0 ≤ σ0) (hLσ : L ≤ σ0)
    (R1 X Y : Lines K m) (hR1s : R1.1 ≤ s) (hR1 : ¬ S R1)
    (hXs : X.1 ≤ s) (hYs : Y.1 ≤ s) (hXY : X ≠ Y) (hSY : S Y)
    (hXt : ¬ X.1 ≤ t0) (hYt : ¬ Y.1 ≤ t0)
    (hsS : ∀ Z : Lines K m, Z.1 ≤ s → S Z → Z = X ∨ Z = Y)
    (hU : ((linesOf σ0).filter S).card = Fintype.card K + 2)
    (htS : ((linesOf t0).filter S).card = 2)
    (hsec : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → M ≤ σ0 →
      ((linesOf M).filter S).card ≤ 2 ∨ Fintype.card K ≤ ((linesOf M).filter S).card)
    (hlR1 : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → M ≤ σ0 → R1.1 ≤ M → M ≠ s →
      ∀ Z Z' : Lines K m, Z.1 ≤ M → Z'.1 ≤ M → S Z → S Z' → Z = Z')
    (hLbig : Fintype.card K ≤ ((linesOf L).filter S).card) (hXL : X.1 ≤ L) : False := by
  classical
  have hq2 : 2 ≤ Fintype.card K := by omega
  have hLt : L ≠ t0 := by rintro rfl; rw [htS] at hLbig; omega
  obtain ⟨D, hDt0, hSD, hDL⟩ := exists_D S t0 L ht hL htS hLt
  have hDX : D ≠ X := fun h => hXt (h ▸ hDt0)
  have hDY : D ≠ Y := fun h => hYt (h ▸ hDt0)
  have hDs : ¬ D.1 ≤ s := fun h => (hsS D h hSD).elim hDX hDY
  have hσmem : ∀ Z : Lines K m, Z.1 ≤ σ0 → S Z → Z ∈ (linesOf σ0).filter S := fun Z h1 h2 => by
    rw [Finset.mem_filter, mem_linesOf]; exact ⟨h1, h2⟩
  have hLsub : (linesOf L).filter S ⊆ (linesOf σ0).filter S := by
    intro Z hZ; rw [Finset.mem_filter, mem_linesOf] at hZ ⊢; exact ⟨hZ.1.trans hLσ, hZ.2⟩
  have hnotin : ∀ Z : Lines K m, ¬ Z.1 ≤ L → Z ∉ (linesOf L).filter S := fun Z h hZ => by
    rw [Finset.mem_filter, mem_linesOf] at hZ; exact h hZ.1
  have hYL : ¬ Y.1 ≤ L := by
    intro hYL
    have hsL : s = L := (two_pts hs hXY hXs hYs).symm.trans (two_pts hL hXY hXL hYL)
    have : (linesOf L).filter S ⊆ {X, Y} := by
      intro Z hZ
      rw [Finset.mem_filter, mem_linesOf, ← hsL] at hZ
      rcases hsS Z hZ.1 hZ.2 with rfl | rfl <;> simp
    have := (Finset.card_le_card this).trans Finset.card_le_two
    omega
  have hYD : Y ≠ D := Ne.symm hDY
  have hout : ∀ Z : Lines K m, Z.1 ≤ σ0 → S Z → ¬ Z.1 ≤ L → Z = Y ∨ Z = D := by
    intro Z hZσ hSZ hZL
    by_contra hcon
    push Not at hcon
    have := card_add_three _ _ Y D Z hLsub (hσmem Y (hYs.trans hsσ) hSY)
      (hσmem D (hDt0.trans htσ) hSD) (hσmem Z hZσ hSZ) (hnotin Y hYL) (hnotin D hDL)
      (hnotin Z hZL) hYD (Ne.symm hcon.1) (Ne.symm hcon.2)
    omega
  have hnon : ∀ N N' : Lines K m, N.1 ≤ L → N'.1 ≤ L → ¬ S N → ¬ S N' → N = N' := by
    intro N N' h1 h2 h3 h4
    by_contra hne
    have hsub : (linesOf L).filter S ⊆ ((linesOf L).erase N).erase N' := by
      intro Z hZ
      rw [Finset.mem_filter] at hZ
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun h => h4 (h ▸ hZ.2), fun h => h3 (h ▸ hZ.2), hZ.1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by rw [Finset.mem_erase, mem_linesOf]; exact ⟨Ne.symm hne, h2⟩),
      Finset.card_erase_of_mem ((mem_linesOf _ _).mpr h1), card_linesOf, hL, th_two _ hq2] at this
    omega
  have hR1D : R1 ≠ D := fun h => hR1 (h ▸ hSD)
  have hM1r : finrank K ↥(R1.1 ⊔ D.1) = 2 := finrank_join hR1D
  have hM1σ : R1.1 ⊔ D.1 ≤ σ0 := sup_le (hR1s.trans hsσ) (hDt0.trans htσ)
  have hM1s : R1.1 ⊔ D.1 ≠ s := fun h => hDs (h ▸ le_sup_right)
  have hM2r : finrank K ↥(Y.1 ⊔ D.1) = 2 := finrank_join hYD
  have hM2σ : Y.1 ⊔ D.1 ≤ σ0 := sup_le (hYs.trans hsσ) (hDt0.trans htσ)
  obtain ⟨N1, hN1M, hN1L⟩ := meet_exists σ0 _ L hσ hM1r hL hM1σ hLσ
  obtain ⟨N2, hN2M, hN2L⟩ := meet_exists σ0 _ L hσ hM2r hL hM2σ hLσ
  have hSN1 : ¬ S N1 := fun h =>
    hDL ((hlR1 _ hM1r hM1σ le_sup_left hM1s N1 D hN1M le_sup_right h hSD) ▸ hN1L)
  have hSN2 : ¬ S N2 := by
    intro h
    have hN2Y : N2 ≠ Y := fun e => hYL (e ▸ hN2L)
    have hN2D : N2 ≠ D := fun e => hDL (e ▸ hN2L)
    have hsub : (linesOf (Y.1 ⊔ D.1)).filter S ⊆ {Y, D, N2} := by
      intro Z hZ
      rw [Finset.mem_filter, mem_linesOf] at hZ
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hZL : Z.1 ≤ L
      · right; right
        by_contra hZN
        have heq : Y.1 ⊔ D.1 = L :=
          (two_pts hM2r hZN hZ.1 hN2M).symm.trans (two_pts hL hZN hZL hN2L)
        exact hYL (by rw [← heq]; exact le_sup_left)
      · rcases hout Z (hZ.1.trans hM2σ) hZ.2 hZL with h' | h'
        · left; exact h'
        · right; left; exact h'
    have hsup : ({Y, D, N2} : Finset (Lines K m)) ⊆ (linesOf (Y.1 ⊔ D.1)).filter S := by
      intro Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
      rw [Finset.mem_filter, mem_linesOf]
      rcases hZ with rfl | rfl | rfl
      · exact ⟨le_sup_left, hSY⟩
      · exact ⟨le_sup_right, hSD⟩
      · exact ⟨hN2M, h⟩
    have h3 : ({Y, D, N2} : Finset (Lines K m)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hN2D)]
      simp [hYD, Ne.symm hN2Y]
    have e3 := le_antisymm (Finset.card_le_card hsub) (Finset.card_le_card hsup)
    rcases hsec _ hM2r hM2σ with h' | h' <;> omega
  have hN12 := hnon N1 N2 hN1L hN2L hSN1 hSN2
  have hDN : D ≠ N1 := fun e => hDL (e ▸ hN1L)
  have hN1M2 : N1.1 ≤ Y.1 ⊔ D.1 := by rw [hN12]; exact hN2M
  have hM12 : R1.1 ⊔ D.1 = Y.1 ⊔ D.1 := (two_pts hM1r hDN le_sup_right hN1M).symm.trans
    (two_pts hM2r hDN le_sup_right hN1M2)
  have hR1Y : R1 ≠ Y := fun e => hR1 (e ▸ hSY)
  have hR1M2 : R1.1 ≤ Y.1 ⊔ D.1 := by rw [← hM12]; exact le_sup_left
  have hsM2 : s = Y.1 ⊔ D.1 := (two_pts hs hR1Y hR1s hYs).symm.trans
    (two_pts hM2r hR1Y hR1M2 le_sup_left)
  exact hDs (by rw [hsM2]; exact le_sup_right)

/-- **The U-configuration** (step 5 of the corrected Observation 2): impossible. -/
theorem u_config (hq : 4 ≤ Fintype.card K) (S : Lines K m → Prop) [DecidablePred S]
    (σ0 s t0 : Submodule K (Fin m → K)) (hσ : finrank K σ0 = 3)
    (hs : finrank K s = 2) (ht : finrank K t0 = 2) (hsσ : s ≤ σ0) (htσ : t0 ≤ σ0)
    (R R1 X Y : Lines K m) (hRt : R.1 ≤ t0) (hR1s : R1.1 ≤ s) (hR1 : ¬ S R1)
    (hXs : X.1 ≤ s) (hYs : Y.1 ≤ s) (hXY : X ≠ Y) (hSX : S X) (hSY : S Y)
    (hXt : ¬ X.1 ≤ t0) (hYt : ¬ Y.1 ≤ t0)
    (hsS : ∀ Z : Lines K m, Z.1 ≤ s → S Z → Z = X ∨ Z = Y)
    (hU : ((linesOf σ0).filter S).card = Fintype.card K + 2)
    (htS : ((linesOf t0).filter S).card = 2)
    (hsec : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → M ≤ σ0 →
      ((linesOf M).filter S).card ≤ 2 ∨ Fintype.card K ≤ ((linesOf M).filter S).card)
    (hlR : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → M ≤ σ0 → R.1 ≤ M → M ≠ t0 →
      ∀ Z Z' : Lines K m, Z.1 ≤ M → Z'.1 ≤ M → S Z → S Z' → Z = Z')
    (hlR1 : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → M ≤ σ0 → R1.1 ≤ M → M ≠ s →
      ∀ Z Z' : Lines K m, Z.1 ≤ M → Z'.1 ≤ M → S Z → S Z' → Z = Z') : False := by
  classical
  have hq2 : 2 ≤ Fintype.card K := by omega
  have hXσ : X.1 ≤ σ0 := hXs.trans hsσ
  by_cases hbig : ∃ L : Submodule K (Fin m → K), finrank K L = 2 ∧ L ≤ σ0 ∧
      Fintype.card K ≤ ((linesOf L).filter S).card
  · obtain ⟨L, hL, hLσ, hLb⟩ := hbig
    have hXYL : X.1 ≤ L ∨ Y.1 ≤ L := by
      by_contra hno
      push Not at hno
      have hLt : L ≠ t0 := by rintro rfl; rw [htS] at hLb; omega
      obtain ⟨D, hDt0, hSD, hDL⟩ := exists_D S t0 L ht hL htS hLt
      have hσmem : ∀ Z : Lines K m, Z.1 ≤ σ0 → S Z → Z ∈ (linesOf σ0).filter S :=
        fun Z h1 h2 => by rw [Finset.mem_filter, mem_linesOf]; exact ⟨h1, h2⟩
      have hLsub : (linesOf L).filter S ⊆ (linesOf σ0).filter S := by
        intro Z hZ; rw [Finset.mem_filter, mem_linesOf] at hZ ⊢; exact ⟨hZ.1.trans hLσ, hZ.2⟩
      have hnotin : ∀ Z : Lines K m, ¬ Z.1 ≤ L → Z ∉ (linesOf L).filter S := fun Z h hZ => by
        rw [Finset.mem_filter, mem_linesOf] at hZ; exact h hZ.1
      have := card_add_three _ _ X Y D hLsub (hσmem X hXσ hSX) (hσmem Y (hYs.trans hsσ) hSY)
        (hσmem D (hDt0.trans htσ) hSD) (hnotin X hno.1) (hnotin Y hno.2) (hnotin D hDL) hXY
        (fun e => hXt (e ▸ hDt0)) (fun e => hYt (e ▸ hDt0))
      omega
    rcases hXYL with h | h
    · exact u_config_L hq S σ0 s t0 L hσ hs ht hL hsσ htσ hLσ R1 X Y hR1s hR1 hXs hYs hXY hSY
        hXt hYt hsS hU htS hsec hlR1 hLb h
    · exact u_config_L hq S σ0 s t0 L hσ hs ht hL hsσ htσ hLσ R1 Y X hR1s hR1 hYs hXs
        (Ne.symm hXY) hSX hYt hXt (fun Z h1 h2 => (hsS Z h1 h2).symm) hU htS hsec hlR1 hLb h
  · push Not at hbig
    have hsmall : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → M ≤ σ0 →
        ((linesOf M).filter S).card ≤ 2 := fun M h1 h2 => by
      rcases hsec M h1 h2 with h | h
      · exact h
      · have := hbig M h1 h2; omega
    have hXU : X ∈ (linesOf σ0).filter S := by
      rw [Finset.mem_filter, mem_linesOf]; exact ⟨hXσ, hSX⟩
    have hU'c : (((linesOf σ0).filter S).erase X).card = Fintype.card K + 1 := by
      rw [Finset.card_erase_of_mem hXU, hU]; rfl
    have hmeet : ∀ Z ∈ ((linesOf σ0).filter S).erase X,
        ∃ W : Lines K m, W.1 ≤ X.1 ⊔ Z.1 ∧ W.1 ≤ t0 := by
      intro Z hZ
      rw [Finset.mem_erase, Finset.mem_filter, mem_linesOf] at hZ
      exact meet_exists σ0 _ t0 hσ (finrank_join (Ne.symm hZ.1)) ht (sup_le hXσ hZ.2.1) htσ
    haveI : Nonempty (Lines K m) := ⟨R⟩
    choose! g hg using hmeet
    have hmaps : ∀ Z ∈ ((linesOf σ0).filter S).erase X, g Z ∈ (linesOf t0).erase R := by
      intro Z hZ
      have hZ' := hZ
      rw [Finset.mem_erase, Finset.mem_filter, mem_linesOf] at hZ'
      rw [Finset.mem_erase, mem_linesOf]
      refine ⟨fun hgR => ?_, (hg Z hZ).2⟩
      have hXZ : X ≠ Z := Ne.symm hZ'.1
      have hRle : R.1 ≤ X.1 ⊔ Z.1 := by rw [← hgR]; exact (hg Z hZ).1
      exact hXZ (hlR _ (finrank_join hXZ) (sup_le hXσ hZ'.2.1) hRle
        (fun h => hXt (by rw [← h]; exact le_sup_left)) X Z le_sup_left le_sup_right hSX hZ'.2.2)
    have hinj : Set.InjOn g (((linesOf σ0).filter S).erase X : Set (Lines K m)) := by
      intro Z1 h1 Z2 h2 heq
      have h1' := h1
      have h2' := h2
      rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter, mem_linesOf] at h1' h2'
      by_contra hne
      have hgX : X ≠ g Z1 := fun e => hXt (by rw [e]; exact (hg Z1 h1).2)
      have hg2 : (g Z1).1 ≤ X.1 ⊔ Z2.1 := by rw [heq]; exact (hg Z2 h2).1
      have e1 : X.1 ⊔ Z1.1 = X.1 ⊔ Z2.1 :=
        (two_pts (finrank_join (Ne.symm h1'.1)) hgX le_sup_left (hg Z1 h1).1).symm.trans
          (two_pts (finrank_join (Ne.symm h2'.1)) hgX le_sup_left hg2)
      have hsub : ({X, Z1, Z2} : Finset (Lines K m)) ⊆ (linesOf (X.1 ⊔ Z1.1)).filter S := by
        intro Z hZ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
        rw [Finset.mem_filter, mem_linesOf]
        rcases hZ with rfl | rfl | rfl
        · exact ⟨le_sup_left, hSX⟩
        · exact ⟨le_sup_right, h1'.2.2⟩
        · exact ⟨by rw [e1]; exact le_sup_right, h2'.2.2⟩
      have h3 : ({X, Z1, Z2} : Finset (Lines K m)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
        simp [Ne.symm h1'.1, Ne.symm h2'.1]
      have := Finset.card_le_card hsub
      have := hsmall _ (finrank_join (Ne.symm h1'.1)) (sup_le hXσ h1'.2.1)
      omega
    have := Finset.card_le_card_of_injOn g (fun Z h => hmaps Z h) hinj
    rw [Finset.card_erase_of_mem ((mem_linesOf _ _).mpr hRt), card_linesOf, ht,
      th_two _ hq2] at this
    omega

open Classical in
/-- `≥ q^{m-3}` support points `Z ⊆ λ \ λ'` from tangents at a centre `C` -/
theorem count_A {p : ℕ} (hm : 3 ≤ m) (c : Lines K m → ZMod p) (C : Lines K m)
    (e : ((Fin m → K) ⧸ C.1) ≃ₗ[K] (Fin (m - 1) → K)) (hC : c C = 0) (κ κ' : Hyp K (m - 1))
    (hne : κ ≠ κ')
    (hex : ∀ lam : Lines K (m - 1), lam.1 ≤ κ.1 → ¬ lam.1 ≤ κ'.1 →
      ∃ ℓ : Lines K m, ℓ.1 ≤ P C e lam ∧ c ℓ ≠ 0) :
    Fintype.card K ^ (m - 3) ≤ (Finset.univ.filter (fun Z : Lines K m => c Z ≠ 0 ∧
      Z.1 ≤ κ.1.comap (piR C e) ∧ ¬ Z.1 ≤ κ'.1.comap (piR C e))).card := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  let D := linesOf κ.1 \ linesOf (κ.1 ⊓ κ'.1)
  have hD : D.card = Fintype.card K ^ (m - 3) := by
    have hsub : linesOf (κ.1 ⊓ κ'.1) ⊆ linesOf κ.1 := by
      intro ℓ; rw [mem_linesOf, mem_linesOf]; exact fun h => h.trans inf_le_left
    have h1 := hyp_inf_rank κ κ' hne
    have hκr : finrank K κ.1 = m - 2 := by have := κ.2; omega
    have h2 : finrank K ↥(κ.1 ⊓ κ'.1) = m - 3 := by omega
    rw [Finset.card_sdiff_of_subset hsub, card_linesOf, card_linesOf, hκr, h2,
      show m - 2 = (m - 3) + 1 by omega, th_succ _ _ hq]
    omega
  have key : ∀ lam ∈ D, ∃ ℓ : Lines K m, ℓ.1 ≤ P C e lam ∧ c ℓ ≠ 0 := by
    intro lam hlam
    simp only [D, Finset.mem_sdiff, mem_linesOf] at hlam
    exact hex lam hlam.1 (fun h => hlam.2 (le_inf hlam.1 h))
  haveI : Nonempty (Lines K m) := ⟨C⟩
  choose! g hg using key
  have hgC : ∀ lam ∈ D, g lam ≠ C := fun lam h he => (hg lam h).2 (he ▸ hC)
  have hmap : ∀ lam (h : lam ∈ D), lineMap C e (g lam) (hgC lam h) = lam := fun lam h =>
    ((le_P_iff_eq C e (g lam) (hgC lam h) lam).mp (hg lam h).1).symm
  rw [← hD]
  apply Finset.card_le_card_of_injOn g
  · intro lam hlam
    have hl := hlam
    simp only [D, Finset.mem_coe, Finset.mem_sdiff, mem_linesOf] at hl
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(hg lam hlam).2, ?_, ?_⟩
    · rw [le_comap_iff C e _ (hgC lam hlam), hmap lam hlam]; exact hl.1
    · rw [le_comap_iff C e _ (hgC lam hlam), hmap lam hlam]
      exact fun h => hl.2 (le_inf hl.1 h)
  · intro l1 h1 l2 h2 he
    apply Subtype.ext
    have b1 : l1.1 = (g l1).1.map (piR C e) := congrArg Subtype.val (hmap l1 h1).symm
    have b2 : l2.1 = (g l2).1.map (piR C e) := congrArg Subtype.val (hmap l2 h2).symm
    rw [b1, b2, he]

open Classical in
/-- support points of `λ₁ \ λ₂` inside a second hyperplane `λ₃ ∋ R`: at most `θ_{m-3}` -/
theorem inter_bound {p : ℕ} (hm : 3 ≤ m) (c : Lines K m → ZMod p) (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (hR : c R = 0) (κ1 κ2 : Hyp K (m - 1))
    (huniq : ∀ lam : Lines K (m - 1), lam.1 ≤ κ1.1 → ¬ lam.1 ≤ κ2.1 →
      ∀ ℓ ℓ' : Lines K m, ℓ.1 ≤ P R e lam → ℓ'.1 ≤ P R e lam → c ℓ ≠ 0 → c ℓ' ≠ 0 → ℓ = ℓ')
    (L3 : Submodule K (Fin m → K)) (h3 : finrank K L3 = m - 1) (hR3 : R.1 ≤ L3)
    (hne : L3 ≠ κ1.1.comap (piR R e)) :
    (Finset.univ.filter (fun Z : Lines K m => (c Z ≠ 0 ∧ Z.1 ≤ κ1.1.comap (piR R e) ∧
      ¬ Z.1 ≤ κ2.1.comap (piR R e)) ∧ Z.1 ≤ L3)).card ≤ th (Fintype.card K) (m - 3) := by
  classical
  have hI := hyp2_inf _ L3 (finrank_comap_hyp R e κ1) h3 hne (by omega)
  have hRI : R.1 ≤ κ1.1.comap (piR R e) ⊓ L3 := le_inf (R_le_comap R e _) hR3
  have hW : finrank K ((κ1.1.comap (piR R e) ⊓ L3).map (piR R e)) = m - 3 := by
    have := finrank_map_piR R e _ hRI; omega
  rw [← hW, ← card_linesOf]
  calc _ ≤ ((linesOf ((κ1.1.comap (piR R e) ⊓ L3).map (piR R e))).image
        (fun μ : Lines K (m - 1) => μ.1)).card := by
        apply Finset.card_le_card_of_injOn (fun ℓ : Lines K m => ℓ.1.map (piR R e))
        · intro ℓ hℓ
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
          have hℓR : ℓ ≠ R := fun h => hℓ.1.1 (h ▸ hR)
          exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨lineMap R e ℓ hℓR,
            (mem_linesOf _ _).mpr (Submodule.map_mono (le_inf hℓ.1.2.1 hℓ.2)), rfl⟩)
        · intro ℓ1 h1 ℓ2 h2 he
          have he' : ℓ1.1.map (piR R e) = ℓ2.1.map (piR R e) := he
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have hℓR : ℓ1 ≠ R := fun h => h1.1.1 (h ▸ hR)
          have hl1 : (lineMap R e ℓ1 hℓR).1 ≤ κ1.1 := (le_comap_iff R e ℓ1 hℓR _).mp h1.1.2.1
          have hl2 : ¬ (lineMap R e ℓ1 hℓR).1 ≤ κ2.1 :=
            fun h => h1.1.2.2 ((le_comap_iff R e ℓ1 hℓR _).mpr h)
          have a1 : ℓ1.1 ≤ P R e (lineMap R e ℓ1 hℓR) := (le_P_iff R e _ ℓ1.1).mpr le_rfl
          have a2 : ℓ2.1 ≤ P R e (lineMap R e ℓ1 hℓR) := by
            rw [le_P_iff]; show ℓ2.1.map (piR R e) ≤ ℓ1.1.map (piR R e); rw [he']
          exact huniq _ hl1 hl2 ℓ1 ℓ2 a1 a2 h1.1.1 h2.1.1
    _ ≤ _ := Finset.card_image_le

theorem arith_final (Q n a1 a2 a3 u i b1 b2 : ℕ) (hQ : 3 ≤ Q) (hA1 : Q ^ n * Q ≤ a1)
    (hA2 : Q ^ n * Q ≤ a2) (hA3 : Q ^ n * Q ≤ a3) (hb1 : b1 ≤ Q ^ n + th Q n)
    (hb2 : b2 ≤ Q ^ n + th Q n) (hu : u + i = a1 + a2 + a3) (hi : i ≤ b1 + b2)
    (hw : u ≤ 3 * (Q ^ n * Q) - 3 * Q ^ n - 1) : False := by
  have hth := th_dvd Q n
  have h2 : 2 * th Q n ≤ (Q - 1) * th Q n := Nat.mul_le_mul_right _ (by omega)
  have hQn : 1 ≤ Q ^ n := Nat.one_le_pow _ _ (by omega)
  have hQQ : 3 * Q ^ n ≤ Q ^ n * Q := by nlinarith
  omega

end obs2geo

open Classical in
/-- **AD21 Observation 2, corrected** (case (2)): no line of `λ₁ = piR⁻¹ κ₁` outside
`τ = piR⁻¹ (κ₁ ∩ κ₂)` is a 2-secant of `supp c` with **both** support points outside `τ`.

The paper's Observation 2 ("all 2-secants in `λ₁` lie in `τ`") is false: in `F^4` take
`c = α₁ W₁ + α₂ W₂` with `W₁ = ⟨e₁, e₂⟩`, `W₂ = ⟨e₃, e₄⟩` (weight `2q + 2 ≤ 3q - 4`) and
`R = ⟨e₁ + e₃⟩`; then `λ₁ = ⟨e₁, e₂, e₃⟩`, `λ₂ = ⟨e₁, e₃, e₄⟩`, `τ = ⟨e₁, e₃⟩`, and
`s = ⟨e₂, e₃⟩ ⊆ λ₁`, `s ⊄ τ` meets `supp c` exactly in `⟨e₂⟩` and `⟨e₃⟩ ∈ τ`. `graph` only needs
the corrected form (both points outside `τ`). (The paper's count of `supp c` outside `λ₁ ∪ λ₂`
is not justified, since the support point of a line `R₁Q`, `Q ∈ κ₃`, may lie in `λ₂ \ τ`.)

Proof (notes/obs2_proof.md, uniform in `p`): both points carry `α₁` and the secant sum gives
`α₂ = α₁ =: α`; `R ∉ s`; `σ₀ = R + s`, `t₀ = σ₀ ∩ τ`; pick `R₁ ∈ s \ ({X, Y} ∪ τ)` and write
`proj_{R₁} c = β₃ κ₃ + β₄ κ₄` (base case). With `T̄` the image of `R`, `d(T̄) = α`,
`d(s̄) = 2α`, `β₃ + β₄ = 2α`, so `T̄` lies in exactly one of `κ₃, κ₄`, say `κₐ`, with `βₐ = α`.
If the image `ℓ̄` of `σ₀` lies in `κₐ`, every line of `σ₀` through `R₁` other than `s` is a
tangent and `u_config` is contradicted; otherwise `count_A`/`inter_bound` give
`wt c ≥ 3q^k - 2θ_k > L_m`. -/
theorem obs2 (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 4 ≤ m) (c : Lines K m → ZMod p)
    (hc : c ∈ Um K m p) (hw : hammingNorm c ≤ Lm (p ^ a) m) (R : Lines K m) (hR : c R = 0)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (κ₁ κ₂ : Hyp K (m - 1))
    (α₁ α₂ : ZMod p) (hne : κ₁ ≠ κ₂) (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0)
    (hproj : proj R e c = α₁ • incH (ZMod p) κ₁ + α₂ • incH (ZMod p) κ₂) :
    ∀ s : Submodule K (Fin m → K), finrank K s = 2 → s ≤ κ₁.1.comap (piR R e) →
      ¬ s ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) →
        2 ≤ ((linesOf s).filter
          (fun ℓ => ¬ ℓ.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) ∧ c ℓ ≠ 0)).card →
        ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≠ 2 := by
  classical
  intro s hs hsL hsτ h2out hcard
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq : 33 ≤ Fintype.card K := by rw [hK]; omega
  have hκ1 := κ₁.2
  have hκ2 := κ₂.2
  -- the total sum `c · 1 = α₁ + α₂`
  have htot : ∑ᶠ ℓ, c ℓ = α₁ + α₂ := by
    rw [← proj_sum p a hK (by omega) R e c, finsum_eq_sum_of_fintype, hproj]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_incH p a hK (d := m - 1) (by omega), mul_one]
  have hsecS : SecH c (α₁ + α₂) := by
    intro t ht
    have := secant hB p a hQ h49 h121 hK hm c hc hw t ht
    rw [htot, ← hK] at this
    exact this
  have hval : ∀ lam : Lines K (m - 1), proj R e c lam =
      (if lam.1 ≤ κ₁.1 then α₁ else 0) + (if lam.1 ≤ κ₂.1 then α₂ else 0) := by
    intro lam
    rw [hproj]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, incH]
    split_ifs <;> simp
  -- tangents through `R` (Observation 1)
  have htan1 : ∀ lam : Lines K (m - 1), lam.1 ≤ κ₁.1 → ¬ lam.1 ≤ κ₂.1 →
      ∃ Z : Lines K m, Z.1 ≤ P R e lam ∧ c Z = α₁ ∧
        ∀ Z' : Lines K m, Z'.1 ≤ P R e lam → c Z' ≠ 0 → Z' = Z := by
    intro lam h1 h2
    refine tanM c _ hsecS (P R e lam) (finrank_P R e lam) R (R_le_P R e lam) hR α₁ hα₁ ?_ ?_
    · intro h
      apply hα₂
      have : α₁ + α₂ = α₁ + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel this
    · rw [← proj_eq_sum, hval, if_pos h1, if_neg h2, add_zero]
  have htan2 : ∀ lam : Lines K (m - 1), lam.1 ≤ κ₂.1 → ¬ lam.1 ≤ κ₁.1 →
      ∃ Z : Lines K m, Z.1 ≤ P R e lam ∧ c Z = α₂ ∧
        ∀ Z' : Lines K m, Z'.1 ≤ P R e lam → c Z' ≠ 0 → Z' = Z := by
    intro lam h1 h2
    refine tanM c _ hsecS (P R e lam) (finrank_P R e lam) R (R_le_P R e lam) hR α₂ hα₂ ?_ ?_
    · intro h
      apply hα₁
      have : 0 + α₂ = α₁ + α₂ := by rw [zero_add]; exact h
      exact (add_right_cancel this).symm
    · rw [← proj_eq_sum, hval, if_neg h2, if_pos h1, zero_add]
  -- the two support points of `s`
  obtain ⟨X, Y, hXY, hF⟩ := Finset.card_eq_two.mp hcard
  have hXF : X ∈ (linesOf s).filter (fun ℓ => c ℓ ≠ 0) := by rw [hF]; simp
  have hYF : Y ∈ (linesOf s).filter (fun ℓ => c ℓ ≠ 0) := by rw [hF]; simp
  rw [Finset.mem_filter, mem_linesOf] at hXF hYF
  have hsS : ∀ Z : Lines K m, Z.1 ≤ s → c Z ≠ 0 → Z = X ∨ Z = Y := by
    intro Z h1 h2
    have : Z ∈ (linesOf s).filter (fun ℓ => c ℓ ≠ 0) := by
      rw [Finset.mem_filter, mem_linesOf]; exact ⟨h1, h2⟩
    rw [hF] at this
    simpa using this
  have hτ12 : (κ₁.1 ⊓ κ₂.1).comap (piR R e) =
      κ₁.1.comap (piR R e) ⊓ κ₂.1.comap (piR R e) := Submodule.comap_inf _ _ _
  have hXYout : ¬ X.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) ∧
      ¬ Y.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) := by
    have hsub : (linesOf s).filter
        (fun ℓ => ¬ ℓ.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) ∧ c ℓ ≠ 0) ⊆
        (linesOf s).filter (fun ℓ => c ℓ ≠ 0) := by
      intro ℓ hℓ
      rw [Finset.mem_filter] at hℓ ⊢
      exact ⟨hℓ.1, hℓ.2.2⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact h2out)
    have hX' : X ∈ (linesOf s).filter
        (fun ℓ => ¬ ℓ.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) ∧ c ℓ ≠ 0) := by rw [heq, hF]; simp
    have hY' : Y ∈ (linesOf s).filter
        (fun ℓ => ¬ ℓ.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) ∧ c ℓ ≠ 0) := by rw [heq, hF]; simp
    rw [Finset.mem_filter] at hX' hY'
    exact ⟨hX'.2.1, hY'.2.1⟩
  -- support points of `λ₁ \ τ` carry `α₁`
  have hval1 : ∀ Z : Lines K m, Z.1 ≤ κ₁.1.comap (piR R e) →
      ¬ Z.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) → c Z ≠ 0 → c Z = α₁ := by
    intro Z h1 h2 h3
    have hZR : Z ≠ R := fun h => h3 (h ▸ hR)
    have l1 : (lineMap R e Z hZR).1 ≤ κ₁.1 := (le_comap_iff R e Z hZR _).mp h1
    have l2 : ¬ (lineMap R e Z hZR).1 ≤ κ₂.1 :=
      fun h => h2 ((le_comap_iff R e Z hZR _).mpr (le_inf l1 h))
    obtain ⟨W, -, hW, hWu⟩ := htan1 _ l1 l2
    rw [hWu Z ((le_P_iff R e _ Z.1).mpr le_rfl) h3]; exact hW
  have hcX := hval1 X (hXF.1.trans hsL) hXYout.1 hXF.2
  have hcY := hval1 Y (hYF.1.trans hsL) hXYout.2 hYF.2
  have hsum_s : ∑ ℓ ∈ linesOf s, c ℓ = α₁ + α₁ := by
    rw [← Finset.sum_filter_ne_zero, hF, Finset.sum_pair hXY, hcX, hcY]
  -- step 1: `α₂ = α₁`
  have hα21 : α₂ = α₁ := by
    have := (hsecS s hs).2.1 hcard
    rw [hsum_s] at this
    exact (add_left_cancel this).symm
  have hα0 : α₁ + α₁ ≠ α₁ := fun h => hα₁ (by
    have : α₁ + α₁ = α₁ + 0 := by rw [add_zero]; exact h
    exact add_left_cancel this)
  -- step 2: `R ∉ s`, the plane `σ₀ = R + s`, the line `t₀ = σ₀ ∩ τ`
  have hXR : X ≠ R := fun h => hXF.2 (h ▸ hR)
  have hRs : ¬ R.1 ≤ s := by
    intro hRs
    have l1 : (lineMap R e X hXR).1 ≤ κ₁.1 := (le_comap_iff R e X hXR _).mp (hXF.1.trans hsL)
    have l2 : ¬ (lineMap R e X hXR).1 ≤ κ₂.1 :=
      fun h => hXYout.1 ((le_comap_iff R e X hXR _).mpr (le_inf l1 h))
    obtain ⟨W, -, -, hWu⟩ := htan1 _ l1 l2
    have hP : P R e (lineMap R e X hXR) = s := by
      rw [plane_eq R e X hXR]; exact two_pts hs (Ne.symm hXR) hRs hXF.1
    have e1 := hWu X (by rw [hP]; exact hXF.1) hXF.2
    have e2 := hWu Y (by rw [hP]; exact hYF.1) hYF.2
    exact hXY (e1.trans e2.symm)
  have hσr : finrank K ↥(s ⊔ R.1) = 3 := by rw [finrank_sup_line s R hRs, hs]
  have hRL1 : R.1 ≤ κ₁.1.comap (piR R e) := R_le_comap R e _
  have hσL1 : s ⊔ R.1 ≤ κ₁.1.comap (piR R e) := sup_le hsL hRL1
  have hRτ : R.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) := R_le_comap R e _
  have hL1r : finrank K (κ₁.1.comap (piR R e)) = m - 1 := finrank_comap_hyp R e κ₁
  have hτr : finrank K ((κ₁.1 ⊓ κ₂.1).comap (piR R e)) = m - 2 := by
    rw [finrank_comap_piR]; have := hyp_inf_rank κ₁ κ₂ hne; omega
  have hτL1 : (κ₁.1 ⊓ κ₂.1).comap (piR R e) ≤ κ₁.1.comap (piR R e) :=
    Submodule.comap_mono inf_le_left
  have ht0r : finrank K ↥((s ⊔ R.1) ⊓ (κ₁.1 ⊓ κ₂.1).comap (piR R e)) = 2 := by
    have hlt : (κ₁.1 ⊓ κ₂.1).comap (piR R e) <
        (s ⊔ R.1) ⊔ (κ₁.1 ⊓ κ₂.1).comap (piR R e) :=
      lt_of_le_of_ne le_sup_right
        (fun h => hsτ (le_sup_left.trans (le_sup_left.trans (le_of_eq h.symm))))
    have a1 := Submodule.finrank_lt_finrank_of_lt hlt
    have a2 : finrank K ↥((s ⊔ R.1) ⊔ (κ₁.1 ⊓ κ₂.1).comap (piR R e)) ≤ m - 1 :=
      (Submodule.finrank_mono (sup_le hσL1 hτL1)).trans hL1r.le
    have a3 := Submodule.finrank_sup_add_finrank_inf_eq (s ⊔ R.1)
      ((κ₁.1 ⊓ κ₂.1).comap (piR R e))
    omega
  have hRt0 : R.1 ≤ (s ⊔ R.1) ⊓ (κ₁.1 ⊓ κ₂.1).comap (piR R e) := le_inf le_sup_right hRτ
  have ht0σ : (s ⊔ R.1) ⊓ (κ₁.1 ⊓ κ₂.1).comap (piR R e) ≤ s ⊔ R.1 := inf_le_left
  have hXt0 : ¬ X.1 ≤ (s ⊔ R.1) ⊓ (κ₁.1 ⊓ κ₂.1).comap (piR R e) :=
    fun h => hXYout.1 (h.trans inf_le_right)
  have hYt0 : ¬ Y.1 ≤ (s ⊔ R.1) ⊓ (κ₁.1 ⊓ κ₂.1).comap (piR R e) :=
    fun h => hXYout.2 (h.trans inf_le_right)
  -- step 3: a second centre `R₁ ∈ s \ ({X, Y} ∪ τ)`
  obtain ⟨R1, hR1s, hR1X, hR1Y, hR1τ⟩ : ∃ R1 : Lines K m, R1.1 ≤ s ∧ R1 ≠ X ∧ R1 ≠ Y ∧
      ¬ R1.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) := by
    by_contra hno
    push Not at hno
    have hsub : linesOf s ⊆ {X, Y} ∪
        (linesOf s).filter (fun ℓ => ℓ.1 ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e)) := by
      intro Z hZ
      rw [mem_linesOf] at hZ
      rw [Finset.mem_union, Finset.mem_filter, mem_linesOf, Finset.mem_insert,
        Finset.mem_singleton]
      by_cases h1 : Z = X
      · left; left; exact h1
      by_cases h2 : Z = Y
      · left; right; exact h2
      right; exact ⟨hZ, hno Z hZ h1 h2⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [card_linesOf, hs, th_two _ hq2] at this
    have := card_filter_le_one s _ hs hsτ
    have := Finset.card_le_two (a := X) (b := Y)
    omega
  have hcR1 : c R1 = 0 := by
    by_contra h
    rcases hsS R1 hR1s h with h' | h'
    · exact hR1X h'
    · exact hR1Y h'
  have hR1R : R1 ≠ R := fun h => hRs (h ▸ hR1s)
  have hRR1 : R ≠ R1 := Ne.symm hR1R
  have hR1L1 : R1.1 ≤ κ₁.1.comap (piR R e) := hR1s.trans hsL
  have hR1L2 : ¬ R1.1 ≤ κ₂.1.comap (piR R e) :=
    fun h => hR1τ (by rw [hτ12]; exact le_inf hR1L1 h)
  have hR1σ : R1.1 ≤ s ⊔ R.1 := hR1s.trans le_sup_left
  obtain ⟨e1⟩ := exists_e R1
  -- the projection from `R₁` is a combination of two hyperplanes (base case)
  have hmem := proj_mem p a hK (by omega) R1 e1 c hc
  have hwt' : hammingNorm (proj R1 e1 c) ≤ Lm (p ^ a) (m - 1 + 1) := by
    rw [show m - 1 + 1 = m by omega]; exact (proj_weight_le R1 e1 c hcR1).trans hw
  obtain ⟨κ3, κ4, β3, β4, hd⟩ := hB p a hQ h49 h121 (m - 1) (by omega) K hK _ hmem hwt'
  have hβ : β3 + β4 = α₁ + α₁ := by
    have hs' := proj_sum p a hK (by omega) R1 e1 c
    rw [htot, hα21, finsum_eq_sum_of_fintype, hd] at hs'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_incH p a hK (d := m - 1) (by omega), mul_one] at hs'
    exact hs'
  have hdv : ∀ lam : Lines K (m - 1), proj R1 e1 c lam =
      (if lam.1 ≤ κ3.1 then β3 else 0) + (if lam.1 ≤ κ4.1 then β4 else 0) := by
    intro lam
    rw [hd]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, incH]
    split_ifs <;> simp
  -- `d(T̄) = α`, `T̄` the image of `R`
  have hdT : proj R1 e1 c (lineMap R1 e1 R hRR1) = α₁ := by
    rw [proj_eq_sum, plane_eq R1 e1 R hRR1, sup_comm, ← plane_eq R e R1 hR1R,
      ← proj_eq_sum, hval, if_pos ((le_comap_iff R e R1 hR1R _).mp hR1L1),
      if_neg (fun h => hR1L2 ((le_comap_iff R e R1 hR1R _).mpr h)), add_zero]
  -- `d(s̄) = 2α`
  let sb : Lines K (m - 1) :=
    ⟨s.map (piR R1 e1), by have := finrank_map_piR R1 e1 s hR1s; omega⟩
  have hPsb : P R1 e1 sb = s := comap_map_piR R1 e1 s hR1s
  have hds : proj R1 e1 c sb = α₁ + α₁ := by rw [proj_eq_sum, hPsb, hsum_s]
  have hlbr : finrank K ((s ⊔ R.1).map (piR R1 e1)) = 2 := by
    have := finrank_map_piR R1 e1 _ hR1σ; omega
  have hTlb : (lineMap R1 e1 R hRR1).1 ≤ (s ⊔ R.1).map (piR R1 e1) :=
    Submodule.map_mono le_sup_right
  have hsblb : sb.1 ≤ (s ⊔ R.1).map (piR R1 e1) := Submodule.map_mono le_sup_left
  -- step 4: the case analysis on `d` along `ℓ̄`
  have main : ∀ (κa κb : Hyp K (m - 1)) (βb : ZMod p),
      (∀ lam : Lines K (m - 1), proj R1 e1 c lam =
        (if lam.1 ≤ κa.1 then α₁ else 0) + (if lam.1 ≤ κb.1 then βb else 0)) →
      (lineMap R1 e1 R hRR1).1 ≤ κa.1 → ¬ (lineMap R1 e1 R hRR1).1 ≤ κb.1 → False := by
    intro κa κb βb hda hTa hTb
    have hab : κa ≠ κb := fun h => hTb (h ▸ hTa)
    by_cases hla : (s ⊔ R.1).map (piR R1 e1) ≤ κa.1
    · -- `ℓ̄ ⊆ κa`: the U-configuration
      have hsbb : sb.1 ≤ κb.1 := by
        by_contra h
        rw [hda, if_pos (hsblb.trans hla), if_neg h, add_zero] at hds
        exact hα0 hds.symm
      have hthR1 : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → R1.1 ≤ M →
          M ≤ s ⊔ R.1 → M ≠ s → ((linesOf M).filter (fun ℓ => c ℓ ≠ 0)).card = 1 := by
        intro M hM hR1M hMσ hMs
        let lm : Lines K (m - 1) :=
          ⟨M.map (piR R1 e1), by have := finrank_map_piR R1 e1 M hR1M; omega⟩
        have hPm : P R1 e1 lm = M := comap_map_piR R1 e1 M hR1M
        have hlm : lm.1 ≤ (s ⊔ R.1).map (piR R1 e1) := Submodule.map_mono hMσ
        have hlmsb : lm ≠ sb := fun h => hMs (by rw [← hPm, h, hPsb])
        have hlmb : ¬ lm.1 ≤ κb.1 := by
          intro h
          apply hTb
          have h2 := two_pts hlbr hlmsb hlm hsblb
          exact hTlb.trans (by rw [← h2]; exact sup_le h hsbb)
        have hdl : ∑ ℓ ∈ linesOf M, c ℓ = α₁ := by
          rw [← hPm, ← proj_eq_sum, hda, if_pos (hlm.trans hla), if_neg hlmb, add_zero]
        obtain ⟨Z, hZM, hcZ, hZu⟩ := tanM c _ hsecS M hM R1 hR1M hcR1 α₁ hα₁
          (by rw [hα21]; exact fun h => hα0 h.symm) hdl
        exact card_one_of c M Z hZM (by rw [hcZ]; exact hα₁) hZu
      have hthR : ∀ M : Submodule K (Fin m → K), finrank K M = 2 → R.1 ≤ M →
          M ≤ s ⊔ R.1 → M ≠ (s ⊔ R.1) ⊓ (κ₁.1 ⊓ κ₂.1).comap (piR R e) →
          ((linesOf M).filter (fun ℓ => c ℓ ≠ 0)).card = 1 := by
        intro M hM hRM hMσ hMt
        have hMτ : ¬ M ≤ (κ₁.1 ⊓ κ₂.1).comap (piR R e) := fun h =>
          hMt (Submodule.eq_of_le_of_finrank_eq (le_inf hMσ h) (by rw [hM, ht0r]))
        let lm : Lines K (m - 1) :=
          ⟨M.map (piR R e), by have := finrank_map_piR R e M hRM; omega⟩
        have hPm : P R e lm = M := comap_map_piR R e M hRM
        have l1 : lm.1 ≤ κ₁.1 := Submodule.map_le_iff_le_comap.mpr (hMσ.trans hσL1)
        have l2 : ¬ lm.1 ≤ κ₂.1 := fun h => hMτ (Submodule.map_le_iff_le_comap.mp (le_inf l1 h))
        obtain ⟨Z, hZM, hcZ, hZu⟩ := htan1 lm l1 l2
        rw [hPm] at hZM hZu
        exact card_one_of c M Z hZM (by rw [hcZ]; exact hα₁) hZu
      have hcU1 := fiber_count R1 (s ⊔ R.1) s hσr hR1σ hs hR1s le_sup_left
        (fun ℓ => c ℓ ≠ 0) (by simp [hcR1]) hthR1
      have hcU2 := fiber_count R (s ⊔ R.1) _ hσr le_sup_right ht0r hRt0 ht0σ
        (fun ℓ => c ℓ ≠ 0) (by simp [hR]) hthR
      rw [hcard] at hcU1
      exact u_config (by omega) (fun ℓ => c ℓ ≠ 0) (s ⊔ R.1) s _ hσr hs ht0r le_sup_left ht0σ
        R R1 X Y hRt0 hR1s (by simp [hcR1]) hXF.1 hYF.1 hXY hXF.2 hYF.2 hXt0 hYt0 hsS
        (by omega) (by omega) (fun M hM _ => (hsecS M hM).1)
        (fun M hM hMσ hRM hMt => le_one_of _ M (hthR M hM hRM hMσ hMt))
        (fun M hM hMσ hR1M hMs => le_one_of _ M (hthR1 M hM hR1M hMσ hMs))
    · -- `ℓ̄ ⊄ κa`: three tangent families, weight count
      have hTa' : R.1 ≤ κa.1.comap (piR R1 e1) := (le_comap_iff R1 e1 R hRR1 _).mpr hTa
      have hLa1 : κa.1.comap (piR R1 e1) ≠ κ₁.1.comap (piR R e) := fun h =>
        hla (Submodule.map_le_iff_le_comap.mpr (by rw [h]; exact hσL1))
      have hLa2 : κa.1.comap (piR R1 e1) ≠ κ₂.1.comap (piR R e) := fun h =>
        hR1L2 (by rw [← h]; exact R_le_comap R1 e1 _)
      have hA1 := count_A (by omega) c R e hR κ₁ κ₂ hne (fun lam h1 h2 => by
        obtain ⟨Z, a1, b1, -⟩ := htan1 lam h1 h2; exact ⟨Z, a1, by rw [b1]; exact hα₁⟩)
      have hA2 := count_A (by omega) c R e hR κ₂ κ₁ (Ne.symm hne) (fun lam h1 h2 => by
        obtain ⟨Z, a1, b1, -⟩ := htan2 lam h1 h2; exact ⟨Z, a1, by rw [b1]; exact hα₂⟩)
      have hA3 := count_A (by omega) c R1 e1 hcR1 κa κb hab (fun lam h1 h2 => by
        have hsum : ∑ ℓ ∈ linesOf (P R1 e1 lam), c ℓ ≠ 0 := by
          rw [← proj_eq_sum, hda, if_pos h1, if_neg h2, add_zero]; exact hα₁
        obtain ⟨Z, hZ, hcZ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
        exact ⟨Z, (mem_linesOf _ _).mp hZ, hcZ⟩)
      have hI1 := inter_bound (by omega) c R e hR κ₁ κ₂ (fun lam h1 h2 ℓ ℓ' a1 a2 a3 a4 => by
          obtain ⟨Z, -, -, hZu⟩ := htan1 lam h1 h2; rw [hZu ℓ a1 a3, hZu ℓ' a2 a4])
        _ (finrank_comap_hyp R1 e1 κa) hTa' hLa1
      have hI2 := inter_bound (by omega) c R e hR κ₂ κ₁ (fun lam h1 h2 ℓ ℓ' a1 a2 a3 a4 => by
          obtain ⟨Z, -, -, hZu⟩ := htan2 lam h1 h2; rw [hZu ℓ a1 a3, hZu ℓ' a2 a4])
        _ (finrank_comap_hyp R1 e1 κa) hTa' hLa2
      set A1 := Finset.univ.filter (fun Z : Lines K m => c Z ≠ 0 ∧
        Z.1 ≤ κ₁.1.comap (piR R e) ∧ ¬ Z.1 ≤ κ₂.1.comap (piR R e)) with hA1d
      set A2 := Finset.univ.filter (fun Z : Lines K m => c Z ≠ 0 ∧
        Z.1 ≤ κ₂.1.comap (piR R e) ∧ ¬ Z.1 ≤ κ₁.1.comap (piR R e)) with hA2d
      set A3 := Finset.univ.filter (fun Z : Lines K m => c Z ≠ 0 ∧
        Z.1 ≤ κa.1.comap (piR R1 e1) ∧ ¬ Z.1 ≤ κb.1.comap (piR R1 e1)) with hA3d
      set B1 := Finset.univ.filter (fun Z : Lines K m => (c Z ≠ 0 ∧
        Z.1 ≤ κ₁.1.comap (piR R e) ∧ ¬ Z.1 ≤ κ₂.1.comap (piR R e)) ∧
          Z.1 ≤ κa.1.comap (piR R1 e1)) with hB1d
      set B2 := Finset.univ.filter (fun Z : Lines K m => (c Z ≠ 0 ∧
        Z.1 ≤ κ₂.1.comap (piR R e) ∧ ¬ Z.1 ≤ κ₁.1.comap (piR R e)) ∧
          Z.1 ≤ κa.1.comap (piR R1 e1)) with hB2d
      have hwt : hammingNorm c = (Finset.univ.filter (fun ℓ : Lines K m => c ℓ ≠ 0)).card := rfl
      have hsub : (A1 ∪ A2) ∪ A3 ⊆ Finset.univ.filter (fun ℓ : Lines K m => c ℓ ≠ 0) := by
        intro Z hZ
        simp only [A1, A2, A3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and] at hZ ⊢
        rcases hZ with (h | h) | h <;> exact h.1
      have hdisj : Disjoint A1 A2 := by
        rw [Finset.disjoint_left]
        intro Z h1 h2
        simp only [A1, A2, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact h1.2.2 h2.2.1
      have hinter : (A1 ∪ A2) ∩ A3 ⊆ B1 ∪ B2 := by
        intro Z hZ
        simp only [A1, A2, A3, B1, B2, Finset.mem_union, Finset.mem_inter, Finset.mem_filter,
          Finset.mem_univ, true_and] at hZ ⊢
        rcases hZ with ⟨h | h, h3⟩
        · left; exact ⟨h, h3.2.1⟩
        · right; exact ⟨h, h3.2.1⟩
      have e1 := Finset.card_union_of_disjoint hdisj
      have e2 := Finset.card_union_add_card_inter (A1 ∪ A2) A3
      have e3 := (Finset.card_le_card hinter).trans (Finset.card_union_le B1 B2)
      have e4 := Finset.card_le_card hsub
      rw [← hwt] at e4
      obtain ⟨n, hn⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
      have hLm : Lm (p ^ a) m = 3 * (Fintype.card K ^ n * Fintype.card K) -
          3 * Fintype.card K ^ n - 1 := by
        rw [Lm, ← hK, hn, show n + 4 - 3 = n + 1 by omega, show n + 4 - 4 = n by omega,
          pow_succ]
      have hm3 : m - 3 = n + 1 := by omega
      rw [hm3, pow_succ] at hA1 hA2 hA3
      rw [hm3, th_succ _ _ hq2] at hI1 hI2
      exact arith_final (Fintype.card K) n A1.card A2.card A3.card ((A1 ∪ A2) ∪ A3).card
        ((A1 ∪ A2) ∩ A3).card B1.card B2.card (by omega) hA1 hA2 hA3 hI1 hI2 (by omega) e3
        (by rw [← hLm]; omega)
  by_cases h3 : (lineMap R1 e1 R hRR1).1 ≤ κ3.1 <;>
    by_cases h4 : (lineMap R1 e1 R hRR1).1 ≤ κ4.1
  · rw [hdv, if_pos h3, if_pos h4, hβ] at hdT; exact hα0 hdT
  · have hb3 : β3 = α₁ := by rw [hdv, if_pos h3, if_neg h4, add_zero] at hdT; exact hdT
    exact main κ3 κ4 β4 (fun lam => by rw [hdv, hb3]) h3 h4
  · have hb4 : β4 = α₁ := by rw [hdv, if_neg h3, if_pos h4, zero_add] at hdT; exact hdT
    exact main κ4 κ3 β3 (fun lam => by rw [hdv, hb4, add_comm]) h4 h3
  · rw [hdv, if_neg h3, if_neg h4, add_zero] at hdT; exact hα₁ hdT.symm

open Classical in
/-- **Incidence-geometric core** (AD21's application of Lemma 5.7 inside `λ₁`), no code or
weight involved. `λ₁ = piR⁻¹ κ`, `τ = piR⁻¹ B` with `B = 0` or `B` a hyperplane of `κ`.
If every plane `R + μ` (`μ ∈ κ \ B`) meets `supp c` in exactly one point, every line meets
`supp c` in `≤ 2` or `≥ q` points, and no line of `λ₁` outside `τ` is a 2-secant with both
support points outside `τ`, then
`supp c ∩ (λ₁ \ τ)` lies in a codimension-two subspace.

Proof sketch: a line `l ⊄ τ` of `λ₁` through two points of `S = supp c ∩ (λ₁ \ τ)` is a
`≥ q`-secant; it cannot miss a point `M ∈ l \ τ` (else, with `Z` the support point of the plane
`R + M`, the line `Z X` for `X ∈ S ∩ l` meets `supp c` in `2` or `3` points), so `S` meets
every line of `λ₁` in `0`, `1` or `q` points; Lemma 5.7 in `λ₁` puts `S` or `λ₁ \ S` in a
hyperplane of `λ₁`, and `|S| ≤ |κ \ B| < q^{m-2} = |λ₁ \ H|` excludes the latter. -/
theorem graph {p : ℕ} {K : Type} [Field K] [Fintype K] {m : ℕ} (hm : 4 ≤ m)
    (hq : 33 ≤ Fintype.card K) (c : Lines K m → ZMod p) (R : Lines K m) (hR : c R = 0)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (κ : Hyp K (m - 1))
    (B : Submodule K (Fin (m - 1) → K)) (hBκ : B ≤ κ.1)
    (hB' : B = ⊥ ∨ finrank K B + 1 = finrank K κ.1)
    (htan : ∀ lam : Lines K (m - 1), lam.1 ≤ κ.1 → ¬ lam.1 ≤ B →
      ∃ ℓ : Lines K m, ℓ.1 ≤ P R e lam ∧ c ℓ ≠ 0 ∧
        ∀ ℓ' : Lines K m, ℓ'.1 ≤ P R e lam → c ℓ' ≠ 0 → ℓ' = ℓ)
    (hsec : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
      ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≤ 2 ∨
        Fintype.card K ≤ ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card)
    (hno2 : ∀ s : Submodule K (Fin m → K), finrank K s = 2 → s ≤ κ.1.comap (piR R e) →
      ¬ s ≤ B.comap (piR R e) →
        2 ≤ ((linesOf s).filter (fun ℓ => ¬ ℓ.1 ≤ B.comap (piR R e) ∧ c ℓ ≠ 0)).card →
          ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≠ 2) :
    ∃ W : Codim2 K m, ∀ ℓ : Lines K m, ℓ.1 ≤ κ.1.comap (piR R e) →
      ¬ ℓ.1 ≤ B.comap (piR R e) → c ℓ ≠ 0 → ℓ.1 ≤ W.1 := by
  classical
  have hq4 : 4 ≤ Fintype.card K := by omega
  set L := κ.1.comap (piR R e) with hL
  set T := B.comap (piR R e) with hT
  have hRT : R.1 ≤ T := by
    intro x hx
    rw [hT, Submodule.mem_comap, (piR_eq_zero R e x).mpr hx]; exact B.zero_mem
  let A : Lines K m → Prop := fun ℓ => ℓ.1 ≤ L ∧ ¬ ℓ.1 ≤ T ∧ c ℓ ≠ 0
  have hAR : ∀ ℓ, A ℓ → ℓ ≠ R := fun ℓ h he => h.2.1 (by rw [he]; exact hRT)
  have hAmap : ∀ ℓ, A ℓ → ℓ.1.map (piR R e) ≤ κ.1 ∧ ¬ ℓ.1.map (piR R e) ≤ B :=
    fun ℓ h => ⟨Submodule.map_le_iff_le_comap.mpr h.1,
      fun h' => h.2.1 (Submodule.map_le_iff_le_comap.mp h')⟩
  have hAinj : ∀ ℓ₁ ℓ₂, A ℓ₁ → A ℓ₂ → ℓ₁.1.map (piR R e) = ℓ₂.1.map (piR R e) → ℓ₁ = ℓ₂ := by
    intro ℓ₁ ℓ₂ h1 h2 he
    obtain ⟨Z, -, -, hZu⟩ := htan (lineMap R e ℓ₁ (hAR ℓ₁ h1)) (hAmap ℓ₁ h1).1 (hAmap ℓ₁ h1).2
    have a1 : ℓ₁.1 ≤ P R e (lineMap R e ℓ₁ (hAR ℓ₁ h1)) := (le_P_iff R e _ ℓ₁.1).mpr le_rfl
    have a2 : ℓ₂.1 ≤ P R e (lineMap R e ℓ₁ (hAR ℓ₁ h1)) := by
      rw [le_P_iff]; show ℓ₂.1.map (piR R e) ≤ ℓ₁.1.map (piR R e); rw [he]
    rw [hZu ℓ₁ a1 h1.2.2, hZu ℓ₂ a2 h2.2.2]
  have hcardA : ∀ U : Submodule K (Fin (m - 1) → K),
      ((linesOf (U.comap (piR R e))).filter A).card ≤ (linesOf U).card := by
    intro U
    calc _ ≤ ((linesOf U).image (fun μ : Lines K (m - 1) => μ.1)).card := by
          apply Finset.card_le_card_of_injOn (fun ℓ : Lines K m => ℓ.1.map (piR R e))
          · intro ℓ hℓ
            simp only [Finset.mem_coe, Finset.mem_filter, mem_linesOf] at hℓ
            refine Finset.mem_coe.mpr (Finset.mem_image.mpr ?_)
            exact ⟨lineMap R e ℓ (hAR ℓ hℓ.2), (mem_linesOf _ _).mpr
              (Submodule.map_le_iff_le_comap.mpr hℓ.1), rfl⟩
          · intro ℓ₁ h1 ℓ₂ h2 he
            simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
            exact hAinj ℓ₁ ℓ₂ h1.2 h2.2 he
      _ ≤ _ := Finset.card_image_le
  have hline : ∀ s : Submodule K (Fin m → K), finrank K s = 2 → s ≤ L → ¬ s ≤ T →
      2 ≤ ((linesOf s).filter A).card →
        Fintype.card K - 1 ≤ ((linesOf s).filter A).card := by
    intro s hs hsL hsT hA2
    have h2 : 2 ≤ ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card :=
      hA2.trans (Finset.card_le_card fun ℓ hℓ => by
        simp only [Finset.mem_filter] at hℓ ⊢; exact ⟨hℓ.1, hℓ.2.2.2⟩)
    have h2' : 2 ≤ ((linesOf s).filter (fun ℓ => ¬ ℓ.1 ≤ T ∧ c ℓ ≠ 0)).card :=
      hA2.trans (Finset.card_le_card fun ℓ hℓ => by
        simp only [Finset.mem_filter] at hℓ ⊢; exact ⟨hℓ.1, hℓ.2.2.1, hℓ.2.2.2⟩)
    have hq' : Fintype.card K ≤ ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card := by
      rcases hsec s hs with h | h
      · exact absurd (le_antisymm h h2) (hno2 s hs hsL hsT h2')
      · exact h
    have hsub : (linesOf s).filter (fun ℓ => c ℓ ≠ 0) ⊆
        (linesOf s).filter A ∪ (linesOf s).filter (fun ℓ => ℓ.1 ≤ T) := by
      intro ℓ hℓ
      simp only [Finset.mem_filter, mem_linesOf, Finset.mem_union] at hℓ ⊢
      by_cases hT' : ℓ.1 ≤ T
      · exact Or.inr ⟨hℓ.1, hT'⟩
      · exact Or.inl ⟨hℓ.1, hℓ.1.trans hsL, hT', hℓ.2⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have := card_filter_le_one s T hs hsT
    omega
  have hA : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
      ((linesOf s).filter A).card ≤ 1 ∨
        Fintype.card K ≤ ((linesOf s).filter A).card := by
    intro s hs
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    obtain ⟨X₁, hX₁, X₂, hX₂, hX12⟩ := Finset.one_lt_card.mp h1
    simp only [Finset.mem_filter, mem_linesOf] at hX₁ hX₂
    have hsX : X₁.1 ⊔ X₂.1 = s := Submodule.eq_of_le_of_finrank_eq (sup_le hX₁.1 hX₂.1)
      (by rw [finrank_join hX12, hs])
    have hsL : s ≤ L := hsX ▸ sup_le hX₁.2.1 hX₂.2.1
    have hsT : ¬ s ≤ T := fun h => hX₁.2.2.1 (hX₁.1.trans h)
    have hl := hline s hs hsL hsT h1
    obtain ⟨M, hMs, hMT, hMc⟩ : ∃ M : Lines K m, M.1 ≤ s ∧ ¬ M.1 ≤ T ∧ c M = 0 := by
      by_contra hno
      push Not at hno
      have hsub : linesOf s ⊆ (linesOf s).filter A ∪ (linesOf s).filter (fun ℓ => ℓ.1 ≤ T) := by
        intro ℓ hℓ
        rw [mem_linesOf] at hℓ
        simp only [Finset.mem_union, Finset.mem_filter, mem_linesOf]
        by_cases hT' : ℓ.1 ≤ T
        · exact Or.inr ⟨hℓ, hT'⟩
        · exact Or.inl ⟨hℓ, hℓ.trans hsL, hT', hno ℓ hℓ hT'⟩
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [card_linesOf, hs, th_two _ (by omega)] at this
      have := card_filter_le_one s T hs hsT
      omega
    have hMR : M ≠ R := fun h => hMT (by rw [h]; exact hRT)
    have hMκ : M.1.map (piR R e) ≤ κ.1 := Submodule.map_le_iff_le_comap.mpr (hMs.trans hsL)
    have hMB : ¬ M.1.map (piR R e) ≤ B := fun h => hMT (Submodule.map_le_iff_le_comap.mp h)
    obtain ⟨Z, hZP, hZc, hZu⟩ := htan (lineMap R e M hMR) hMκ hMB
    have hZR : Z ≠ R := fun h => hZc (by rw [h]; exact hR)
    have hZmap : Z.1.map (piR R e) = M.1.map (piR R e) :=
      (congrArg Subtype.val ((le_P_iff_eq R e Z hZR _).mp hZP)).symm
    have hZA : A Z := by
      refine ⟨?_, ?_, hZc⟩
      · rw [← Submodule.map_le_iff_le_comap, hZmap]; exact hMκ
      · intro h; apply hMB; rw [← hZmap]; exact Submodule.map_le_iff_le_comap.mpr h
    have hMP : M.1 ≤ P R e (lineMap R e M hMR) := (le_P_iff R e _ M.1).mpr le_rfl
    have hZs : ¬ Z.1 ≤ s := by
      intro hZs
      have hZM : Z ≠ M := fun h => hZc (by rw [h]; exact hMc)
      have e1 : Z.1 ⊔ M.1 = s := Submodule.eq_of_le_of_finrank_eq (sup_le hZs hMs)
        (by rw [finrank_join hZM, hs])
      have e2 : Z.1 ⊔ M.1 = P R e (lineMap R e M hMR) :=
        Submodule.eq_of_le_of_finrank_eq (sup_le hZP hMP) (by rw [finrank_join hZM, finrank_P])
      have hsP : s ≤ P R e (lineMap R e M hMR) := by rw [← e1, e2]
      exact hX12 ((hZu X₁ (hX₁.1.trans hsP) hX₁.2.2.2).trans
        (hZu X₂ (hX₂.1.trans hsP) hX₂.2.2.2).symm)
    have hZX : Z ≠ X₁ := fun h => hZs (by rw [h]; exact hX₁.1)
    have hs₂r : finrank K ↥(Z.1 ⊔ X₁.1) = 2 := finrank_join hZX
    have hs₂L : Z.1 ⊔ X₁.1 ≤ L := sup_le hZA.1 hX₁.2.1
    have hs₂T : ¬ Z.1 ⊔ X₁.1 ≤ T := fun h => hX₁.2.2.1 (le_sup_right.trans h)
    have hsupp2' : 2 ≤ ((linesOf (Z.1 ⊔ X₁.1)).filter A).card := by
      have : ({Z, X₁} : Finset (Lines K m)) ⊆ (linesOf (Z.1 ⊔ X₁.1)).filter A := by
        intro ℓ hℓ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
        rw [Finset.mem_filter, mem_linesOf]
        rcases hℓ with rfl | rfl
        · exact ⟨le_sup_left, hZA⟩
        · exact ⟨le_sup_right, hX₁.2⟩
      have := Finset.card_le_card this
      rwa [Finset.card_pair hZX] at this
    have hl2 := hline _ hs₂r hs₂L hs₂T hsupp2'
    have hsσ : s ≤ (s.map (piR R e)).comap (piR R e) := Submodule.le_comap_map _ _
    have hZσ : Z.1 ≤ (s.map (piR R e)).comap (piR R e) := by
      rw [← Submodule.map_le_iff_le_comap, hZmap]; exact Submodule.map_mono hMs
    have hs₂σ : Z.1 ⊔ X₁.1 ≤ (s.map (piR R e)).comap (piR R e) := sup_le hZσ (hX₁.1.trans hsσ)
    have hσc : ((linesOf ((s.map (piR R e)).comap (piR R e))).filter A).card ≤
        Fintype.card K + 1 := by
      have h1 := hcardA (s.map (piR R e))
      rw [card_linesOf] at h1
      have h2 : finrank K (s.map (piR R e)) ≤ 2 := hs ▸ Submodule.finrank_map_le _ _
      have := th_mono (Fintype.card K) (by omega) h2
      rw [th_two _ (by omega)] at this
      omega
    have hdisj : Disjoint (((linesOf (Z.1 ⊔ X₁.1)).filter A).erase X₁) ((linesOf s).filter A) := by
      rw [Finset.disjoint_left]
      intro Y hY1 hY2
      simp only [Finset.mem_erase, Finset.mem_filter, mem_linesOf] at hY1 hY2
      exact hY1.1 (join_inf hX₁.1 hZs hY2.1 hY1.2.1)
    have hsub : ((linesOf (Z.1 ⊔ X₁.1)).filter A).erase X₁ ∪ (linesOf s).filter A ⊆
        (linesOf ((s.map (piR R e)).comap (piR R e))).filter A := by
      intro Y hY
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, mem_linesOf] at hY ⊢
      rcases hY with h | h
      · exact ⟨h.2.1.trans hs₂σ, h.2.2⟩
      · exact ⟨h.1.trans hsσ, h.2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hc
    have hX₁A : X₁ ∈ (linesOf (Z.1 ⊔ X₁.1)).filter A := by
      rw [Finset.mem_filter, mem_linesOf]; exact ⟨le_sup_right, hX₁.2⟩
    rw [Finset.card_erase_of_mem hX₁A] at hc
    omega
  have hLr : finrank K L = (m - 2) + 1 := by
    rw [hL, finrank_comap_piR]; have := κ.2; omega
  obtain ⟨H, hHL, hHr, hcase⟩ := gen hq4 (m - 2) A hA L hLr
  refine ⟨⟨H, by omega⟩, ?_⟩
  rcases hcase with h | h
  · intro ℓ h1 h2 h3; exact h ℓ h1 ⟨h1, h2, h3⟩
  · exfalso
    have hsub : linesOf L \ linesOf H ⊆ (linesOf L).filter A := by
      intro ℓ hℓ
      simp only [Finset.mem_sdiff, mem_linesOf, Finset.mem_filter] at hℓ ⊢
      exact ⟨hℓ.1, by_contra fun hn => hℓ.2 (h ℓ hℓ.1 hn)⟩
    have hHsub : linesOf H ⊆ linesOf L := fun ℓ => by
      rw [mem_linesOf, mem_linesOf]; exact fun h' => h'.trans hHL
    have h1 := Finset.card_le_card hsub
    have hHr' : finrank K H = m - 2 := by omega
    rw [Finset.card_sdiff_of_subset hHsub, card_linesOf, card_linesOf, hLr, hHr',
      th_succ _ _ (by omega)] at h1
    have h2 : ((linesOf L).filter A).card ≤ (linesOf κ.1).card := hcardA κ.1
    rw [card_linesOf] at h2
    have hκr : finrank K κ.1 = m - 2 := by have := κ.2; omega
    rw [hκr] at h2
    have := th_lt (Fintype.card K) (m - 2) (by omega)
    omega

/-! ## AD21 Lemma 5.8 -/

theorem chk_half_value (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 4 ≤ m) (c : Lines K m → ZMod p)
    (hc : c ∈ Um K m p) (hw : hammingNorm c ≤ Lm (p ^ a) m) (R : Lines K m) (hR : c R = 0)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (κ₁ κ₂ : Hyp K (m - 1))
    (α₁ α₂ : ZMod p)
    (h : κ₁ ≠ κ₂ ∧ α₁ ≠ 0 ∧ α₂ ≠ 0 ∧
          proj R e c = α₁ • incH (ZMod p) κ₁ + α₂ • incH (ZMod p) κ₂) :
    ∃ W : Codim2 K m, ∃ α : ZMod p, α ≠ 0 ∧
      (linesOf W.1).card < 2 * ((linesOf W.1).filter (fun ℓ => c ℓ = α)).card := by
  classical
  have hm1 : 3 ≤ m - 1 := by omega
  have hκ1 := κ₁.2
  have hκ2 := κ₂.2
  -- the total sum `c · 1`
  have htot : ∑ᶠ ℓ, c ℓ = ∑ᶠ lam, proj R e c lam := (proj_sum p a hK (by omega) R e c).symm
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at htot
  obtain ⟨hne, hα₁, hα₂, hproj⟩ := h
  · -- case (2)
    have hsum1 : ∑ lam, proj R e c lam = α₁ + α₂ := by
      rw [hproj]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, sum_incH p a hK (d := m - 1) (by omega), mul_one]
    have hBr : finrank K ↥(κ₁.1 ⊓ κ₂.1) + 1 = finrank K κ₁.1 := by
      -- `κ₁ ∩ κ₂` is a hyperplane of `κ₁`
      have hlt : κ₁.1 < κ₁.1 ⊔ κ₂.1 := by
        refine lt_of_le_of_ne le_sup_left fun heq => hne ?_
        have hle : κ₂.1 ≤ κ₁.1 := by rw [heq]; exact le_sup_right
        exact (Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by omega))).symm
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2 : finrank K ↥(κ₁.1 ⊔ κ₂.1) ≤ m - 1 := by
        have := Submodule.finrank_le (κ₁.1 ⊔ κ₂.1)
        rwa [Module.finrank_fin_fun] at this
      have h3 := Submodule.finrank_sup_add_finrank_inf_eq κ₁.1 κ₂.1
      omega
    have htan : ∀ lam : Lines K (m - 1), lam.1 ≤ κ₁.1 → ¬ lam.1 ≤ κ₁.1 ⊓ κ₂.1 →
        ∃ ℓ : Lines K m, ℓ.1 ≤ P R e lam ∧ c ℓ = α₁ ∧
          ∀ ℓ' : Lines K m, ℓ'.1 ≤ P R e lam → c ℓ' ≠ 0 → ℓ' = ℓ := by
      intro lam hl1 hl2
      have hl2' : ¬ lam.1 ≤ κ₂.1 := fun h => hl2 (le_inf hl1 h)
      have hval : proj R e c lam = α₁ := by
        rw [hproj]
        simp [incH, hl1, hl2']
      have hsec := secant hB p a hQ h49 h121 hK hm c hc hw (P R e lam) (finrank_P R e lam)
      exact tangent R e c hR lam α₁ hα₁ (by rw [← proj_eq_sum, hval])
        (by rw [hK]; exact ⟨hsec.1, hsec.2.2⟩) (by
          intro h2
          have := hsec.2.1 h2
          rw [← proj_eq_sum, hval, finsum_eq_sum_of_fintype, htot, hsum1] at this
          apply hα₂
          have h' : α₁ + α₂ = α₁ + 0 := by rw [add_zero]; exact this.symm
          exact add_left_cancel h')
    obtain ⟨W, hW⟩ := graph hm (by rw [hK]; omega) c R hR e κ₁ (κ₁.1 ⊓ κ₂.1) inf_le_left
      (Or.inr hBr)
      (fun lam h1 h2 => by
        obtain ⟨ℓ, a1, a2, a3⟩ := htan lam h1 h2
        exact ⟨ℓ, a1, by rw [a2]; exact hα₁, a3⟩)
      (fun s hs => by
        have := secant hB p a hQ h49 h121 hK hm c hc hw s hs
        rw [hK]; exact this.1)
      (obs2 hB p a hQ h49 h121 hK hm c hc hw R hR e κ₁ κ₂ α₁ α₂ hne hα₁ hα₂ hproj)
    refine ⟨W, α₁, hα₁, finish hm c R hR e κ₁ (κ₁.1 ⊓ κ₂.1) inf_le_left (by omega) α₁ hα₁
      (fun lam h1 h2 => by
        obtain ⟨ℓ, a1, a2, -⟩ := htan lam h1 h2
        exact ⟨ℓ, a1, a2⟩) W hW⟩

end ProxGapTight.Dev.Q350.Half

namespace ProxGapTight.Dev.Q350
open ProxGapTight

theorem half_value : type_of% @Half.chk_half_value := @Half.chk_half_value

end ProxGapTight.Dev.Q350
end

section
/-!
q350, AD21 Theorem 5.9 (case `n = k + 2`): the induction step from the base case.

Minimal counterexample `c` (strong induction on the weight):
* Observation 1 (`chk_step`): no codimension-two `W` has more than half of its points with one
  nonzero value, else `c - α u_W` is lighter, hence a 2-combination, and `three_weight_gt`.
* (P1) (`main`): every projection from a point off the support is `σ · κ` (`σ = Σ c`), since
  (P2) contradicts Observation 1 through `half_value`.
* Tangent lines: all support values equal `σ`.
* `p = 2`: no 2-secants, so Lemma 5.7 twice puts the support in a codim-2 `W`.
* `p` odd: the `x₁, x₂, x₃` count with `λ = piR⁻¹ κ`,
  `λ' = piR'⁻¹ κ'` and `W = λ ∩ λ'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.Q350.Step
open ProxGapTight ProxGapTight.Dev.Q350 Module

/-! ## Arithmetic -/

def th (Q d : ℕ) : ℕ := (Q ^ d - 1) / (Q - 1)

theorem th_dvd (Q d : ℕ) : (Q - 1) * th Q d = Q ^ d - 1 := by
  unfold th
  have : Q - 1 ∣ Q ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow Q 1 d
  exact Nat.mul_div_cancel' this

theorem th_succ (Q d : ℕ) (hQ : 2 ≤ Q) : th Q (d + 1) = Q ^ d + th Q d := by
  have h1 := th_dvd Q d
  have h2 := th_dvd Q (d + 1)
  have hP : 1 ≤ Q ^ d := Nat.one_le_pow _ _ (by omega)
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 2 := ⟨Q - 2, by omega⟩
  have e1 : Q' + 2 - 1 = Q' + 1 := by omega
  rw [e1] at h1 h2
  rw [pow_succ] at h2
  set P := (Q' + 2) ^ d
  have hr : (Q' + 1) * (P + th (Q' + 2) d) = (Q' + 1) * P + (P - 1) := by
    rw [Nat.mul_add, h1]
  have : (Q' + 1) * th (Q' + 2) (d + 1) = (Q' + 1) * (P + th (Q' + 2) d) := by
    rw [h2, hr]
    have : P * (Q' + 2) = (Q' + 1) * P + P := by ring
    omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

theorem th_mono (Q : ℕ) (hQ : 1 ≤ Q) {d d' : ℕ} (h : d ≤ d') : th Q d ≤ th Q d' := by
  unfold th
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right hQ h

/-! ## Lines -/

section geo
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

theorem mem_linesOf (U : Submodule K (Fin m → K)) (ℓ : Lines K m) :
    ℓ ∈ linesOf U ↔ ℓ.1 ≤ U := by
  classical
  simp [linesOf]

theorem card_linesOf (U : Submodule K (Fin m → K)) :
    (linesOf U).card = th (Fintype.card K) (finrank K U) := by
  classical
  let f : Projectivization K U → Lines K m := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  haveI : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (linesOf U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_linesOf]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ (finrank K U) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), Nat.card_eq_fintype_card]
  rw [hc]
  rfl

/-- `Q = p^a` vanishes in `ZMod p` -/
theorem card_cast_zero (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) :
    ((Fintype.card K : ℕ) : ZMod p) = 0 := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hK] at h1
    simp at h1
  rw [hK]
  push_cast
  rw [ZMod.natCast_self, zero_pow ha]

theorem card_linesOf_cast (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a)
    (U : Submodule K (Fin m → K)) (hU : 1 ≤ finrank K U) :
    ((linesOf U).card : ZMod p) = 1 := by
  rw [card_linesOf U]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  unfold th
  rw [← Nat.geomSum_eq h2]
  push_cast
  rw [card_cast_zero p a hK]
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K U = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hU).symm⟩
  rw [hn, Finset.sum_range_succ']
  simp

theorem line_eq_of_le {ℓ ℓ' : Lines K m} (h : ℓ.1 ≤ ℓ'.1) : ℓ = ℓ' :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (by rw [ℓ.2, ℓ'.2]))

theorem finrank_line_inf {ℓ : Lines K m} {U : Submodule K (Fin m → K)} (h : ¬ ℓ.1 ≤ U) :
    finrank K ↥(ℓ.1 ⊓ U) = 0 := by
  have h1 : finrank K ↥(ℓ.1 ⊓ U) ≤ finrank K ℓ.1 := Submodule.finrank_mono inf_le_left
  rw [ℓ.2] at h1
  by_contra h0
  have e : finrank K ↥(ℓ.1 ⊓ U) = finrank K ℓ.1 := by rw [ℓ.2]; omega
  have e2 := Submodule.eq_of_le_of_finrank_eq inf_le_left e
  apply h
  rw [← e2]
  exact inf_le_right

theorem finrank_sup_line (U : Submodule K (Fin m → K)) (ℓ : Lines K m) (h : ¬ ℓ.1 ≤ U) :
    finrank K ↥(U ⊔ ℓ.1) = finrank K U + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U ℓ.1
  have h0 := finrank_line_inf h
  rw [inf_comm] at h0
  rw [h0, ℓ.2] at h1
  omega

/-! ## The projection -/

/-- the projection map `F^m → F^m / R ≃ F^(m-1)` -/
noncomputable def piR (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    (Fin m → K) →ₗ[K] (Fin (m - 1) → K) := e.toLinearMap ∘ₗ R.1.mkQ

/-- the plane `R + λ` -/
def Pl (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : Submodule K (Fin m → K) :=
  (lam.1.comap e.toLinearMap).comap R.1.mkQ

theorem mem_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) (x : Fin m → K) : x ∈ Pl R e lam ↔ piR R e x ∈ lam.1 := Iff.rfl

theorem piR_eq_zero (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (x : Fin m → K) : piR R e x = 0 ↔ x ∈ R.1 := by
  simp [piR, Submodule.Quotient.mk_eq_zero]

theorem piR_surj (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) :
    Function.Surjective (piR R e) := by
  intro y
  obtain ⟨q, rfl⟩ := e.surjective y
  obtain ⟨x, rfl⟩ := R.1.mkQ_surjective q
  exact ⟨x, rfl⟩

theorem le_P_iff (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) (U : Submodule K (Fin m → K)) :
    U ≤ Pl R e lam ↔ U.map (piR R e) ≤ lam.1 := by
  rw [Submodule.map_le_iff_le_comap]
  rfl

theorem R_le_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : R.1 ≤ Pl R e lam := by
  intro x hx
  rw [mem_P, (piR_eq_zero R e x).mpr hx]
  exact lam.1.zero_mem

theorem finrank_map_line (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : Module.finrank K (ℓ.1.map (piR R e)) = 1 := by
  have h1 : Module.finrank K (ℓ.1.map (piR R e)) ≤ 1 := by
    have := Submodule.finrank_map_le (piR R e) ℓ.1
    rw [ℓ.2] at this
    exact this
  have h2 : ℓ.1.map (piR R e) ≠ ⊥ := by
    intro hb
    apply h
    apply line_eq_of_le
    intro x hx
    have hx' : piR R e x ∈ ℓ.1.map (piR R e) := Submodule.mem_map_of_mem hx
    rw [hb] at hx'
    exact (piR_eq_zero R e x).mp ((Submodule.mem_bot K).mp hx')
  have h3 : Module.finrank K (ℓ.1.map (piR R e)) ≠ 0 := by
    rwa [Ne, Submodule.finrank_eq_zero]
  omega

/-- the image line -/
noncomputable def lineMap (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) : Lines K (m - 1) :=
  ⟨ℓ.1.map (piR R e), finrank_map_line R e ℓ h⟩

theorem le_P_iff_eq (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (ℓ : Lines K m) (h : ℓ ≠ R) (lam : Lines K (m - 1)) :
    ℓ.1 ≤ Pl R e lam ↔ lam = lineMap R e ℓ h := by
  rw [le_P_iff]
  constructor
  · intro hle
    exact (line_eq_of_le (ℓ := lineMap R e ℓ h) hle).symm
  · rintro rfl
    exact le_rfl

theorem proj_eq_sum {p : ℕ} (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (v : Lines K m → ZMod p)
    (lam : Lines K (m - 1)) :
    proj R e v lam = ∑ ℓ ∈ linesOf (Pl R e lam), v ℓ := by
  unfold proj Pl linesOf
  rfl

theorem finrank_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : finrank K (Pl R e lam) = 2 := by
  have hne : lam.1 ≠ ⊥ := by
    intro hb; have := lam.2; rw [hb, finrank_bot] at this; exact zero_ne_one this
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨w, hw⟩ := piR_surj R e v
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; exact hv0 hw.symm
  let ℓw : Lines K m := ⟨K ∙ w, finrank_span_singleton hw0⟩
  have hwR : w ∉ R.1 := by
    intro h; apply hv0; rw [← hw]; exact (piR_eq_zero R e w).mpr h
  have hnle : ¬ ℓw.1 ≤ R.1 := fun h => hwR (h (Submodule.mem_span_singleton_self w))
  have hlam : lam.1 = K ∙ v := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; simpa using hv
    · rw [finrank_span_singleton hv0, lam.2]
  have heq : Pl R e lam = R.1 ⊔ ℓw.1 := by
    apply le_antisymm
    · intro x hx
      rw [mem_P, hlam, Submodule.mem_span_singleton] at hx
      obtain ⟨a, ha⟩ := hx
      have h0 : piR R e (x - a • w) = 0 := by
        rw [map_sub, map_smul, hw, ha, sub_self]
      have hxR := (piR_eq_zero R e _).mp h0
      have : x = (x - a • w) + a • w := by abel
      rw [this]
      exact Submodule.add_mem_sup hxR
        (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w))
    · apply sup_le (R_le_P R e lam)
      rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      show piR R e x ∈ lam.1
      rw [hw]; exact hv
  rw [heq, finrank_sup_line R.1 ℓw hnle, R.2]

theorem card_P (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (lam : Lines K (m - 1)) : (linesOf (Pl R e lam)).card = Fintype.card K + 1 := by
  rw [card_linesOf, finrank_P]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [th_succ _ 1 h2, pow_one]
  unfold th
  simp only [pow_one]
  rw [Nat.div_self (by omega)]

/-! ## Observation 1 / 3: tangent planes through `R` -/

/-- `∑_λ incH κ λ = 1` -/
theorem sum_incH (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a) {d : ℕ} (hd : 2 ≤ d)
    (κ : Hyp K d) : ∑ lam : Lines K d, incH (ZMod p) κ lam = 1 := by
  classical
  have : ∑ lam : Lines K d, incH (ZMod p) κ lam = ((linesOf κ.1).card : ZMod p) := by
    unfold incH linesOf
    rw [Finset.sum_boole]
  rw [this, card_linesOf_cast p a hK]
  have := κ.2; omega

end geo

theorem th_ge (Q d : ℕ) (hQ : 2 ≤ Q) : Q ^ d ≤ th Q (d + 1) := by
  rw [th_succ Q d hQ]; omega

/-! ## More geometry -/

section geo2
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

theorem line_eq_of_small {U : Submodule K (Fin m → K)} (hU : finrank K U ≤ 1)
    {P P' : Lines K m} (h1 : P.1 ≤ U) (h2 : P'.1 ≤ U) : P = P' := by
  have e1 : P.1 = U := Submodule.eq_of_le_of_finrank_le h1 (by rw [P.2]; exact hU)
  have e2 : P'.1 = U := Submodule.eq_of_le_of_finrank_le h2 (by rw [P'.2]; exact hU)
  exact Subtype.ext (e1.trans e2.symm)

theorem finrank_join {R P : Lines K m} (h : R ≠ P) : finrank K ↥(R.1 ⊔ P.1) = 2 := by
  have hX : ¬ P.1 ≤ R.1 := fun hle => h (line_eq_of_le hle).symm
  rw [finrank_sup_line R.1 P hX, R.2]

theorem inf_small {R P : Lines K m} {L : Submodule K (Fin m → K)} (hR : ¬ R.1 ≤ L)
    (hP : P.1 ≤ L) : finrank K ↥((R.1 ⊔ P.1) ⊓ L) ≤ 1 := by
  have hne : R ≠ P := fun h => hR (h ▸ hP)
  have hlt : (R.1 ⊔ P.1) ⊓ L < R.1 ⊔ P.1 := by
    refine lt_of_le_of_ne inf_le_left (fun h => hR ?_)
    have : R.1 ≤ (R.1 ⊔ P.1) ⊓ L := by rw [h]; exact le_sup_left
    exact this.trans inf_le_right
  have := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_join hne] at this
  omega

theorem plane_eq (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (P : Lines K m) (h : P ≠ R) : Pl R e (lineMap R e P h) = R.1 ⊔ P.1 :=
  (Submodule.eq_of_le_of_finrank_eq (sup_le (R_le_P R e _) ((le_P_iff_eq R e P h _).mpr rfl))
    (by rw [finrank_join (Ne.symm h), finrank_P])).symm

theorem le_comap_iff (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (P : Lines K m) (h : P ≠ R) (U : Submodule K (Fin (m - 1) → K)) :
    P.1 ≤ U.comap (piR R e) ↔ (lineMap R e P h).1 ≤ U := by
  rw [← Submodule.map_le_iff_le_comap]; rfl

theorem R_le_comap (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (U : Submodule K (Fin (m - 1) → K)) : R.1 ≤ U.comap (piR R e) := by
  intro x hx
  show piR R e x ∈ U
  rw [(piR_eq_zero R e x).mpr hx]
  exact zero_mem _

theorem finrank_comap_hyp (R : Lines K m)
    (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) (κ : Hyp K (m - 1)) :
    finrank K (κ.1.comap (piR R e)) = m - 1 := by
  set L := κ.1.comap (piR R e) with hL
  have h1 := LinearMap.finrank_range_add_finrank_ker ((piR R e).domRestrict L)
  have hr : LinearMap.range ((piR R e).domRestrict L) = κ.1 := by
    rw [LinearMap.range_domRestrict]
    exact Submodule.map_comap_eq_of_surjective (piR_surj R e) _
  have hkR : LinearMap.ker (piR R e) = R.1 := by
    ext x; rw [LinearMap.mem_ker, piR_eq_zero]
  have hk : LinearMap.ker ((piR R e).domRestrict L) = R.1.comap L.subtype := by
    rw [LinearMap.ker_domRestrict, hkR]
  have hRL : R.1 ≤ L := R_le_comap R e κ.1
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hRL).finrank_eq, R.2] at h1
  have := κ.2
  omega

theorem exists_e (R : Lines K m) :
    Nonempty (((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)) := by
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  have := Submodule.finrank_quotient_add_finrank R.1
  rw [R.2, Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun]; omega

theorem exists_sub (V : Submodule K (Fin m → K)) (k : ℕ) (hk : k ≤ finrank K V) :
    ∃ W ≤ V, finrank K W = k := by
  let b := Module.finBasis K V
  let f : Fin k → (Fin m → K) := fun i => (b (Fin.castLE hk i) : Fin m → K)
  have hli : LinearIndependent K f := by
    have := b.linearIndependent.comp _ (Fin.castLE_injective hk)
    exact this.map' V.subtype (Submodule.ker_subtype V)
  refine ⟨Submodule.span K (Set.range f), ?_, ?_⟩
  · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (b _).2
  · rw [finrank_span_eq_card hli, Fintype.card_fin]

theorem codim2_nonempty (hm : 2 ≤ m) : Nonempty (Codim2 K m) := by
  obtain ⟨W, -, hW⟩ := exists_sub (⊤ : Submodule K (Fin m → K)) (m - 2)
    (by rw [finrank_top, Module.finrank_fin_fun]; omega)
  exact ⟨⟨W, by omega⟩⟩

/-- planes through `R`, indexed by the quotient: disjoint fibres -/
theorem fiber_le (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K))
    (T : Finset (Lines K (m - 1))) (F : Lines K (m - 1) → Finset (Lines K m))
    (X : Finset (Lines K m)) (hF : ∀ μ ∈ T, ∀ ℓ ∈ F μ, ℓ.1 ≤ Pl R e μ ∧ ℓ ≠ R ∧ ℓ ∈ X) :
    ∑ μ ∈ T, (F μ).card ≤ X.card := by
  classical
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro ℓ hℓ
    rw [Finset.mem_biUnion] at hℓ
    obtain ⟨μ, hμ, hℓ⟩ := hℓ
    exact (hF μ hμ ℓ hℓ).2.2
  · intro μ hμ μ' hμ' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ℓ h1 h2
    obtain ⟨a1, b1, -⟩ := hF μ hμ ℓ h1
    obtain ⟨a2, -, -⟩ := hF μ' hμ' ℓ h2
    exact hne (((le_P_iff_eq R e ℓ b1 μ).mp a1).trans ((le_P_iff_eq R e ℓ b1 μ').mp a2).symm)

/-- planes `R + P` for points `P` of a subspace `L ∌ R`: disjoint fibres -/
theorem fiber_le2 (R : Lines K m) (L : Submodule K (Fin m → K)) (hR : ¬ R.1 ≤ L)
    (Y : Finset (Lines K m)) (hY : ∀ P ∈ Y, P.1 ≤ L)
    (F : Lines K m → Finset (Lines K m)) (X : Finset (Lines K m))
    (hF : ∀ P ∈ Y, ∀ ℓ ∈ F P, ℓ.1 ≤ R.1 ⊔ P.1 ∧ ℓ ≠ R ∧ ℓ ∈ X) :
    ∑ P ∈ Y, (F P).card ≤ X.card := by
  classical
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro ℓ hℓ
    rw [Finset.mem_biUnion] at hℓ
    obtain ⟨P, hP, hℓ⟩ := hℓ
    exact (hF P hP ℓ hℓ).2.2
  · intro P hP P' hP' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ℓ h1 h2
    obtain ⟨a1, b1, -⟩ := hF P hP ℓ h1
    obtain ⟨a2, -, -⟩ := hF P' hP' ℓ h2
    have hPR : R ≠ P := fun h => hR (h ▸ hY P hP)
    have hP'R : R ≠ P' := fun h => hR (h ▸ hY P' hP')
    have e1 : R.1 ⊔ ℓ.1 = R.1 ⊔ P.1 := Submodule.eq_of_le_of_finrank_eq
      (sup_le le_sup_left a1) (by rw [finrank_join (Ne.symm b1), finrank_join hPR])
    have e2 : R.1 ⊔ ℓ.1 = R.1 ⊔ P'.1 := Submodule.eq_of_le_of_finrank_eq
      (sup_le le_sup_left a2) (by rw [finrank_join (Ne.symm b1), finrank_join hP'R])
    apply hne
    apply line_eq_of_small (inf_small hR (hY P hP)) (le_inf le_sup_right (hY P hP))
    rw [← e1, e2]
    exact le_inf le_sup_right (hY P' hP')

end geo2

/-! ## AD21 Lemma 5.7 (copied from `Q350Hyp`) -/

theorem th_one (Q : ℕ) (hQ : 2 ≤ Q) : th Q 1 = 1 := by
  unfold th; simp only [pow_one]; exact Nat.div_self (by omega)

theorem th_two (Q : ℕ) (hQ : 2 ≤ Q) : th Q 2 = Q + 1 := by
  rw [th_succ Q 1 hQ, th_one Q hQ, pow_one]

/-- `2((q-1)q^n + 1) > θ_{n+2}` for `q ≥ 4` -/
theorem arith (q n : ℕ) (hq : 4 ≤ q) : th q (n + 2) < 2 * ((q - 1) * q ^ n + 1) := by
  have h := th_dvd q (n + 2)
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 4 := ⟨q - 4, by omega⟩
  have e1 : r + 4 - 1 = r + 3 := by omega
  rw [e1] at h ⊢
  have hQ : 1 ≤ (r + 4) ^ n := Nat.one_le_pow _ _ (by omega)
  have e2 : (r + 4) ^ (n + 2) = (r + 4) ^ n * (r + 4) ^ 2 := by ring
  rw [e2] at h
  set Q := (r + 4) ^ n
  by_contra hcon
  push Not at hcon
  have h3 : (r + 3) * (2 * ((r + 3) * Q + 1)) ≤ (r + 3) * th (r + 4) (n + 2) :=
    Nat.mul_le_mul_left _ hcon
  have h4 : 1 ≤ Q * (r + 4) ^ 2 := by nlinarith
  have h5 : (r + 3) * th (r + 4) (n + 2) + 1 = Q * (r + 4) ^ 2 := by omega
  nlinarith

section geo3
variable {K : Type} [Field K] [Fintype K] {m : ℕ}

/-- a point `ℓ ≠ P` on the line `P X` spans it with `P` -/
theorem join_eq {P X ℓ : Lines K m} (hPX : P ≠ X) (hℓ : ℓ.1 ≤ P.1 ⊔ X.1) (hℓP : ℓ ≠ P) :
    P.1 ⊔ ℓ.1 = P.1 ⊔ X.1 :=
  Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_left hℓ)
    (by rw [finrank_join hPX, finrank_join (Ne.symm hℓP)])

/-- the line `P X` meets `π` only in `X` when `X ∈ π ∌ P` -/
theorem join_inf {P X Y : Lines K m} {π : Submodule K (Fin m → K)} (hX : X.1 ≤ π)
    (hP : ¬ P.1 ≤ π) (hY : Y.1 ≤ π) (hYl : Y.1 ≤ P.1 ⊔ X.1) : Y = X := by
  by_contra hne
  have hPX : P ≠ X := fun e => hP (e ▸ hX)
  have e := Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_right hYl :
      X.1 ⊔ Y.1 ≤ P.1 ⊔ X.1)
    (by rw [finrank_join hPX, finrank_join (Ne.symm hne)])
  apply hP
  calc P.1 ≤ P.1 ⊔ X.1 := le_sup_left
    _ = X.1 ⊔ Y.1 := e.symm
    _ ≤ π := sup_le hX hY

/-! ## The counting step -/

theorem count_lower (A : Lines K m → Prop) [DecidablePred A]
    (hA : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
      2 ≤ ((linesOf s).filter A).card → Fintype.card K ≤ ((linesOf s).filter A).card)
    (V π H : Submodule K (Fin m → K)) (n : ℕ) (hπ : π ≤ V) (hπr : finrank K π = n + 1)
    (hH : H ≤ π) (hHr : finrank K H = n)
    (hAπ : ∀ ℓ : Lines K m, ℓ.1 ≤ π → ¬ ℓ.1 ≤ H → A ℓ)
    (P : Lines K m) (hP : A P) (hPV : P.1 ≤ V) (hPπ : ¬ P.1 ≤ π) :
    (Fintype.card K - 1) * Fintype.card K ^ n + 1 ≤ ((linesOf V).filter A).card := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  set q := Fintype.card K with hqd
  let D := linesOf π \ linesOf H
  have hD : D.card = q ^ n := by
    have hsub : linesOf H ⊆ linesOf π := by
      intro ℓ; rw [mem_linesOf, mem_linesOf]; exact fun h => h.trans hH
    rw [Finset.card_sdiff_of_subset hsub, card_linesOf, card_linesOf, hπr, hHr,
      th_succ q n hq]
    simp only [← hqd]
    omega
  let F : Lines K m → Finset (Lines K m) := fun X => ((linesOf (P.1 ⊔ X.1)).filter A).erase P
  have hmemD : ∀ X ∈ D, X.1 ≤ π ∧ ¬ X.1 ≤ H := by
    intro X hX
    simp only [D, Finset.mem_sdiff, mem_linesOf] at hX
    exact hX
  have hF : ∀ X ∈ D, q - 1 ≤ (F X).card := by
    intro X hX
    obtain ⟨hXπ, hXH⟩ := hmemD X hX
    have hPX : P ≠ X := fun e => hPπ (e ▸ hXπ)
    have h2 : 2 ≤ ((linesOf (P.1 ⊔ X.1)).filter A).card := by
      have : ({P, X} : Finset (Lines K m)) ⊆ (linesOf (P.1 ⊔ X.1)).filter A := by
        intro ℓ hℓ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
        rw [Finset.mem_filter, mem_linesOf]
        rcases hℓ with rfl | rfl
        · exact ⟨le_sup_left, hP⟩
        · exact ⟨le_sup_right, hAπ _ hXπ hXH⟩
      have := Finset.card_le_card this
      rwa [Finset.card_pair hPX] at this
    have hq' := hA _ (finrank_join hPX) h2
    have hmem : P ∈ (linesOf (P.1 ⊔ X.1)).filter A := by
      rw [Finset.mem_filter, mem_linesOf]; exact ⟨le_sup_left, hP⟩
    rw [Finset.card_erase_of_mem hmem]
    omega
  have hdisj : ∀ X ∈ D, ∀ Y ∈ D, X ≠ Y → Disjoint (F X) (F Y) := by
    intro X hX Y hY hXY
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    simp only [F, Finset.mem_erase, Finset.mem_filter, mem_linesOf] at h1 h2
    have hXπ := (hmemD X hX).1
    have hYπ := (hmemD Y hY).1
    have hPX : P ≠ X := fun e => hPπ (e ▸ hXπ)
    have hPY : P ≠ Y := fun e => hPπ (e ▸ hYπ)
    have e1 := join_eq hPX h1.2.1 h1.1
    have e2 := join_eq hPY h2.2.1 h2.1
    have hYle : Y.1 ≤ P.1 ⊔ X.1 := by rw [← e1, e2]; exact le_sup_right
    exact hXY (join_inf hXπ hPπ hYπ hYle).symm
  have hU : (q - 1) * q ^ n ≤ (D.biUnion F).card := by
    rw [Finset.card_biUnion hdisj]
    have := Finset.card_nsmul_le_sum D (fun X => (F X).card) (q - 1) hF
    rw [smul_eq_mul, hD] at this
    linarith
  have hPU : P ∉ D.biUnion F := by
    simp [F]
  have hsub : insert P (D.biUnion F) ⊆ (linesOf V).filter A := by
    intro ℓ hℓ
    rw [Finset.mem_insert] at hℓ
    rw [Finset.mem_filter, mem_linesOf]
    rcases hℓ with rfl | hℓ
    · exact ⟨hPV, hP⟩
    · rw [Finset.mem_biUnion] at hℓ
      obtain ⟨X, hX, hℓX⟩ := hℓ
      simp only [F, Finset.mem_erase, Finset.mem_filter, mem_linesOf] at hℓX
      exact ⟨hℓX.2.1.trans (sup_le hPV ((hmemD X hX).1.trans hπ)), hℓX.2.2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hPU] at this
  omega

/-- the inductive step, for one of `A`, `Aᶜ` -/
theorem main_count (A : Lines K m → Prop) [DecidablePred A]
    (hA : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
      2 ≤ ((linesOf s).filter A).card → Fintype.card K ≤ ((linesOf s).filter A).card)
    (n : ℕ) (V : Submodule K (Fin m → K)) (hV : finrank K V = n + 2)
    (IH : ∀ π : Submodule K (Fin m → K), π ≤ V → finrank K π = n + 1 →
      ∃ H ≤ π, finrank K H + 1 = finrank K π ∧
        ((∀ ℓ : Lines K m, ℓ.1 ≤ π → A ℓ → ℓ.1 ≤ H) ∨
          (∀ ℓ : Lines K m, ℓ.1 ≤ π → ¬ A ℓ → ℓ.1 ≤ H)))
    (hnot : ∀ π : Submodule K (Fin m → K), π ≤ V → finrank K π = n + 1 →
      ∃ ℓ : Lines K m, ℓ.1 ≤ V ∧ A ℓ ∧ ¬ ℓ.1 ≤ π) :
    (Fintype.card K - 1) * Fintype.card K ^ n + 1 ≤ ((linesOf V).filter A).card := by
  classical
  haveI : Finite (Submodule K (Fin m → K)) :=
    Finite.of_injective (fun p : Submodule K (Fin m → K) => (p : Set (Fin m → K)))
      SetLike.coe_injective
  let S : Set (Submodule K (Fin m → K)) := {π | π ≤ V ∧ finrank K π = n + 1}
  let T := (Set.toFinite S).toFinset
  obtain ⟨π0, hπ0V, hπ0r⟩ := exists_sub V (n + 1) (by omega)
  have hTne : T.Nonempty := ⟨π0, by simp [T, S, hπ0V, hπ0r]⟩
  obtain ⟨π, hπT, hmax⟩ := Finset.exists_max_image T (fun π => ((linesOf π).filter A).card) hTne
  simp only [T, S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hπT hmax
  obtain ⟨hπV, hπr⟩ := hπT
  obtain ⟨H, hHπ, hHr, hcase⟩ := IH π hπV hπr
  obtain ⟨X, hXV, hXA, hXπ⟩ := hnot π hπV hπr
  rcases hcase with hc | hc
  · exfalso
    have hXH : ¬ X.1 ≤ H := fun h => hXπ (h.trans hHπ)
    have hr : finrank K ↥(H ⊔ X.1) = n + 1 := by rw [finrank_sup_line H X hXH]; omega
    have hle := hmax (H ⊔ X.1) ⟨sup_le (hHπ.trans hπV) hXV, hr⟩
    have hss : (linesOf π).filter A ⊂ (linesOf (H ⊔ X.1)).filter A := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨X, ?_, ?_⟩
        · rw [Finset.mem_filter, mem_linesOf]; exact ⟨le_sup_right, hXA⟩
        · rw [Finset.mem_filter, mem_linesOf]; exact fun h => hXπ h.1
      · intro ℓ hℓ
        rw [Finset.mem_filter, mem_linesOf] at hℓ ⊢
        exact ⟨(hc ℓ hℓ.1 hℓ.2).trans le_sup_left, hℓ.2⟩
    have := Finset.card_lt_card hss
    omega
  · refine count_lower A hA V π H n hπV hπr hHπ (by omega) ?_ X hXA hXV hXπ
    intro ℓ hℓπ hℓH
    by_contra hn
    exact hℓH (hc ℓ hℓπ hn)

theorem gen (hq : 4 ≤ Fintype.card K) (n : ℕ) :
    ∀ (A : Lines K m → Prop) [DecidablePred A],
      (∀ s : Submodule K (Fin m → K), finrank K s = 2 →
        ((linesOf s).filter A).card ≤ 1 ∨ Fintype.card K ≤ ((linesOf s).filter A).card) →
      ∀ V : Submodule K (Fin m → K), finrank K V = n + 1 →
        ∃ H ≤ V, finrank K H + 1 = finrank K V ∧
          ((∀ ℓ : Lines K m, ℓ.1 ≤ V → A ℓ → ℓ.1 ≤ H) ∨
            (∀ ℓ : Lines K m, ℓ.1 ≤ V → ¬ A ℓ → ℓ.1 ≤ H)) := by
  induction n with
  | zero =>
    intro A _ _ V hV
    refine ⟨⊥, bot_le, by rw [finrank_bot, hV], ?_⟩
    by_cases hex : ∃ ℓ : Lines K m, ℓ.1 ≤ V ∧ A ℓ
    · obtain ⟨ℓ, hℓV, hℓA⟩ := hex
      right
      intro ℓ' hℓ'V hℓ'A
      exfalso
      have e1 := Submodule.eq_of_le_of_finrank_eq hℓV (by rw [ℓ.2, hV])
      have e2 := Submodule.eq_of_le_of_finrank_eq hℓ'V (by rw [ℓ'.2, hV])
      have : ℓ' = ℓ := Subtype.ext (e2.trans e1.symm)
      exact hℓ'A (this ▸ hℓA)
    · left
      intro ℓ hℓV hℓA
      exact absurd ⟨ℓ, hℓV, hℓA⟩ hex
  | succ n ih =>
    intro A _ hA V hV
    classical
    have hq2 : 2 ≤ Fintype.card K := by omega
    by_contra hcon
    push Not at hcon
    -- `hcon : ∀ H ≤ V, finrank H + 1 = finrank V → (∃ ...) ∧ (∃ ...)`
    have hA1 : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
        2 ≤ ((linesOf s).filter A).card → Fintype.card K ≤ ((linesOf s).filter A).card := by
      intro s hs h2
      rcases hA s hs with h | h
      · omega
      · exact h
    have hA2 : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
        2 ≤ ((linesOf s).filter (fun ℓ => ¬ A ℓ)).card →
          Fintype.card K ≤ ((linesOf s).filter (fun ℓ => ¬ A ℓ)).card := by
      intro s hs h2
      have htot := Finset.card_filter_add_card_filter_not (s := linesOf s) A
      rw [card_linesOf, hs, th_two _ hq2] at htot
      rcases hA s hs with h | h
      · omega
      · omega
    have c1 := main_count A hA1 n V hV
      (fun π hπ hπr => ih A hA π hπr)
      (fun π hπ hπr => by
        obtain ⟨⟨ℓ, h1, h2, h3⟩, _⟩ := hcon π hπ (by omega)
        exact ⟨ℓ, h1, h2, h3⟩)
    have c2 := main_count (fun ℓ => ¬ A ℓ) hA2 n V hV
      (fun π hπ hπr => by
        obtain ⟨H, h1, h2, h3⟩ := ih A hA π hπr
        refine ⟨H, h1, h2, ?_⟩
        rcases h3 with h | h
        · right; intro ℓ hℓ hn; exact h ℓ hℓ (not_not.mp hn)
        · left; exact h)
      (fun π hπ hπr => by
        obtain ⟨_, ⟨ℓ, h1, h2, h3⟩⟩ := hcon π hπ (by omega)
        exact ⟨ℓ, h1, h2, h3⟩)
    have htot := Finset.card_filter_add_card_filter_not (s := linesOf V) A
    rw [card_linesOf, hV, show n + 1 + 1 = n + 2 from rfl] at htot
    have := arith (Fintype.card K) n hq
    omega

/-- if every point of `V` off the support lies in the hyperplane `H` of `V`, the weight is at
least `|V \ H| = Q^(dim H)` -/
theorem compl_count {p : ℕ} (c : Lines K m → ZMod p) (V H : Submodule K (Fin m → K))
    (hHV : H ≤ V) (hr : finrank K H + 1 = finrank K V)
    (h : ∀ ℓ : Lines K m, ℓ.1 ≤ V → ¬ (c ℓ ≠ 0) → ℓ.1 ≤ H) :
    Fintype.card K ^ finrank K H ≤ hammingNorm c := by
  classical
  have hsub : linesOf V \ linesOf H ⊆ Finset.univ.filter (fun ℓ => c ℓ ≠ 0) := by
    intro ℓ hℓ
    simp only [Finset.mem_sdiff, mem_linesOf] at hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h0
    exact hℓ.2 (h ℓ hℓ.1 (not_not.mpr h0))
  have h1 := Finset.card_le_card hsub
  have hs : linesOf H ⊆ linesOf V := by
    intro ℓ; rw [mem_linesOf, mem_linesOf]; exact fun h => h.trans hHV
  rw [Finset.card_sdiff_of_subset hs, card_linesOf, card_linesOf, ← hr,
    th_succ _ _ Fintype.one_lt_card] at h1
  have hn : hammingNorm c = (Finset.univ.filter (fun ℓ => c ℓ ≠ 0)).card := rfl
  omega

end geo3

/-! ## The minimal counterexample -/

theorem main (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 4 ≤ m) (c : Lines K m → ZMod p)
    (hc : c ∈ Um K m p) (hw : hammingNorm c ≤ Lm (p ^ a) m) (hc0 : c ≠ 0)
    (hobs : ¬ ∃ W : Codim2 K m, ∃ α : ZMod p, α ≠ 0 ∧
      (linesOf W.1).card < 2 * ((linesOf W.1).filter (fun ℓ => c ℓ = α)).card) : False := by
  classical
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hQ33 : 33 ≤ Fintype.card K := by omega
  obtain ⟨n, hn⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
  -- the weight bound
  have hX1 : 1 ≤ Fintype.card K ^ n * Fintype.card K := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hLm : hammingNorm c + 1 ≤ 3 * (Fintype.card K ^ n * Fintype.card K) := by
    have h1 : Lm (p ^ a) m = 3 * (Fintype.card K ^ n * Fintype.card K) -
        3 * Fintype.card K ^ n - 1 := by
      rw [Lm, ← hK, hn, show n + 4 - 3 = n + 1 by omega, show n + 4 - 4 = n by omega, pow_succ]
    rw [h1] at hw
    omega
  have hwt : hammingNorm c = (Finset.univ.filter (fun ℓ : Lines K m => c ℓ ≠ 0)).card := rfl
  obtain ⟨σ, hσ⟩ : ∃ σ : ZMod p, σ = ∑ᶠ ℓ, c ℓ := ⟨_, rfl⟩
  have hm1 : m - 1 + 1 = m := by omega
  -- (P1): every projection from a point off the support is `σ κ`
  have hP1 : ∀ (R : Lines K m) (e : ((Fin m → K) ⧸ R.1) ≃ₗ[K] (Fin (m - 1) → K)), c R = 0 →
      ∃ κ : Hyp K (m - 1), proj R e c = σ • incH (ZMod p) κ := by
    intro R e hR
    have hmem := proj_mem p a hK (by omega) R e c hc
    have hwt' : hammingNorm (proj R e c) ≤ Lm (p ^ a) (m - 1 + 1) := by
      rw [hm1]; exact (proj_weight_le R e c hR).trans hw
    obtain ⟨H, H', β₁, β₂, hHH⟩ := hB p a hQ h49 h121 (m - 1) (by omega) K hK _ hmem hwt'
    have hγ : ∃ (κ : Hyp K (m - 1)) (γ : ZMod p), proj R e c = γ • incH (ZMod p) κ := by
      by_cases h1 : H = H'
      · subst h1; exact ⟨H, β₁ + β₂, by rw [hHH, add_smul]⟩
      by_cases h2 : β₁ = 0
      · exact ⟨H', β₂, by rw [hHH, h2, zero_smul, zero_add]⟩
      by_cases h3 : β₂ = 0
      · exact ⟨H, β₁, by rw [hHH, h3, zero_smul, add_zero]⟩
      exact absurd (half_value hB p a hQ h49 h121 hK hm c hc hw R hR e H H' β₁ β₂
        ⟨h1, h2, h3, hHH⟩) hobs
    obtain ⟨κ, γ, hκ⟩ := hγ
    refine ⟨κ, ?_⟩
    have hs := proj_sum p a hK (by omega) R e c
    rw [hκ, finsum_eq_sum_of_fintype] at hs
    have : ∑ lam, (γ • incH (ZMod p) κ) lam = γ := by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, sum_incH p a hK (by omega) κ, mul_one]
    rw [this, ← hσ] at hs
    rw [hκ, hs]
  -- tangent lines: every support value is `σ`
  have hall : ∀ P : Lines K m, c P ≠ 0 → c P = σ := by
    intro P hP
    obtain ⟨eP⟩ := exists_e P
    by_cases htan : ∃ μ : Lines K (m - 1), ∀ ℓ : Lines K m, ℓ.1 ≤ Pl P eP μ → c ℓ ≠ 0 → ℓ = P
    · obtain ⟨μ, hμ⟩ := htan
      obtain ⟨R, hRmem, hRP⟩ := Finset.exists_mem_ne
        (show 1 < (linesOf (Pl P eP μ)).card by rw [card_P]; omega) P
      rw [mem_linesOf] at hRmem
      have hR : c R = 0 := by
        by_contra h; exact hRP (hμ R hRmem h)
      obtain ⟨e⟩ := exists_e R
      obtain ⟨κ, hκ⟩ := hP1 R e hR
      have hPR : P ≠ R := Ne.symm hRP
      have hval : proj R e c (lineMap R e P hPR) = c P := by
        rw [proj_eq_sum, plane_eq]
        apply Finset.sum_eq_single_of_mem P ((mem_linesOf _ _).mpr le_sup_right)
        intro ℓ hℓ hne
        by_contra h
        apply hne
        apply hμ ℓ _ h
        rw [mem_linesOf] at hℓ
        exact hℓ.trans (sup_le hRmem (R_le_P P eP μ))
      rw [hκ, Pi.smul_apply, smul_eq_mul] at hval
      unfold incH at hval
      split_ifs at hval with h
      · rw [← hval, mul_one]
      · rw [mul_zero] at hval; exact absurd hval.symm hP
    · exfalso
      push Not at htan
      have hfib := fiber_le P eP (linesOf ⊤)
        (fun μ => (linesOf (Pl P eP μ)).filter (fun ℓ => c ℓ ≠ 0 ∧ ℓ ≠ P))
        ((Finset.univ.filter (fun ℓ => c ℓ ≠ 0)).erase P) (by
          intro μ _ ℓ hℓ
          simp only [Finset.mem_filter, mem_linesOf] at hℓ
          refine ⟨hℓ.1, hℓ.2.2, ?_⟩
          simp [hℓ.2.1, hℓ.2.2])
      have h1 : ∀ μ ∈ linesOf (⊤ : Submodule K (Fin (m - 1) → K)),
          1 ≤ ((linesOf (Pl P eP μ)).filter (fun ℓ => c ℓ ≠ 0 ∧ ℓ ≠ P)).card := by
        intro μ _
        obtain ⟨ℓ, h1, h2, h3⟩ := htan μ
        exact Finset.card_pos.mpr ⟨ℓ, by simp [mem_linesOf, h1, h2, h3]⟩
      have h2 := Finset.card_nsmul_le_sum _ _ 1 h1
      rw [smul_eq_mul, mul_one, card_linesOf, finrank_top, Module.finrank_fin_fun] at h2
      rw [Finset.card_erase_of_mem (by simp [hP])] at hfib
      have h2' := h2.trans hfib
      rw [show m - 1 = (n + 2) + 1 by omega] at h2'
      have h3 := th_ge (Fintype.card K) (n + 2) hq2
      have h4 : Fintype.card K ^ (n + 2) =
          (Fintype.card K ^ n * Fintype.card K) * Fintype.card K := by ring
      have h5 : (Fintype.card K ^ n * Fintype.card K) * 33 ≤
          (Fintype.card K ^ n * Fintype.card K) * Fintype.card K := Nat.mul_le_mul_left _ hQ33
      omega
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, c P₀ ≠ 0 := by
    by_contra h; push Not at h; exact hc0 (funext h)
  have hσ0 : σ ≠ 0 := hall P₀ hP₀ ▸ hP₀
  -- points off a subspace of codimension ≥ 1 and off the support
  have hfree : ∀ L : Submodule K (Fin m → K), finrank K L ≤ m - 1 →
      ∃ R : Lines K m, ¬ R.1 ≤ L ∧ c R = 0 := by
    intro L hL
    have hlt : (linesOf L ∪ Finset.univ.filter (fun ℓ : Lines K m => c ℓ ≠ 0)).card <
        (linesOf (⊤ : Submodule K (Fin m → K))).card := by
      refine (Finset.card_union_le _ _).trans_lt ?_
      rw [← hwt, card_linesOf, card_linesOf, finrank_top, Module.finrank_fin_fun]
      have h1 := th_mono (Fintype.card K) (by omega) hL
      rw [show m - 1 = n + 3 by omega] at h1
      rw [show th (Fintype.card K) m = th (Fintype.card K) (n + 3 + 1) by rw [hn],
        th_succ _ (n + 3) hq2]
      have h4 : Fintype.card K ^ (n + 3) =
          (Fintype.card K ^ n * Fintype.card K) * (Fintype.card K * Fintype.card K) := by ring
      have h5 : (Fintype.card K ^ n * Fintype.card K) * 3 ≤
          (Fintype.card K ^ n * Fintype.card K) * (Fintype.card K * Fintype.card K) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      omega
    obtain ⟨R, -, hR⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_not, mem_linesOf] at hR
    exact ⟨R, hR.1, hR.2⟩
  obtain ⟨R, -, hR⟩ := hfree ⊥ (by simp)
  obtain ⟨e⟩ := exists_e R
  obtain ⟨κ, hκ⟩ := hP1 R e hR
  -- `λ = piR⁻¹ κ`, a second center `R' ∉ λ`, `λ' = piR'⁻¹ κ'`, `W = λ ∩ λ'`
  set L := κ.1.comap (piR R e) with hL
  have hLr : finrank K L = m - 1 := finrank_comap_hyp R e κ
  obtain ⟨R', hR'L, hR'⟩ := hfree L hLr.le
  obtain ⟨e'⟩ := exists_e R'
  obtain ⟨κ', hκ'⟩ := hP1 R' e' hR'
  set L' := κ'.1.comap (piR R' e') with hL'
  have hL'r : finrank K L' = m - 1 := finrank_comap_hyp R' e' κ'
  have hR'L' : R'.1 ≤ L' := R_le_comap R' e' κ'.1
  have hWr : finrank K ↥(L ⊓ L') + 2 = m := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq L L'
    have h2 : finrank K ↥(L ⊔ L') ≤ m :=
      (Submodule.finrank_le _).trans (by rw [Module.finrank_fin_fun])
    have h3 : L < L ⊔ L' := lt_of_le_of_ne le_sup_left
      (fun h => hR'L (by rw [h]; exact hR'L'.trans le_sup_right))
    have h4 := Submodule.finrank_lt_finrank_of_lt h3
    omega
  let W : Codim2 K m := ⟨L ⊓ L', hWr⟩
  have hW1 : W.1 = L ⊓ L' := rfl
  set θ := th (Fintype.card K) (m - 2) with hθ
  have hθW : (linesOf W.1).card = θ := by
    rw [card_linesOf]; congr 1; have := W.2; omega
  -- the sum of `c` over the plane `R' + P`, for `P ∈ λ`
  have hsumP : ∀ P : Lines K m, P.1 ≤ L →
      ∑ ℓ ∈ linesOf (R'.1 ⊔ P.1), c ℓ = if P.1 ≤ L' then σ else 0 := by
    intro P hP
    have hPR' : P ≠ R' := fun h => hR'L (h ▸ hP)
    have h1 := congrFun hκ' (lineMap R' e' P hPR')
    rw [proj_eq_sum, plane_eq, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    unfold incH
    by_cases h : P.1 ≤ L'
    · have h' := (le_comap_iff R' e' P hPR' κ'.1).mp h
      rw [if_pos h', if_pos h, mul_one]
    · have h' : ¬ (lineMap R' e' P hPR').1 ≤ κ'.1 := fun h'' =>
        h ((le_comap_iff R' e' P hPR' κ'.1).mpr h'')
      rw [if_neg h', if_neg h, mul_zero]
  -- the sets
  let S := Finset.univ.filter (fun ℓ : Lines K m => c ℓ ≠ 0)
  let A := (linesOf L).filter (fun ℓ => c ℓ ≠ 0)
  let D := S.filter (fun ℓ => ¬ ℓ.1 ≤ L)
  let Y := (linesOf W.1).filter (fun ℓ => c ℓ ≠ 0)
  let B := A.filter (fun ℓ => ¬ ℓ.1 ≤ W.1)
  let C := (linesOf W.1).filter (fun ℓ => ¬ c ℓ ≠ 0)
  have hAD : A.card + D.card = hammingNorm c := by
    rw [hwt, ← Finset.card_filter_add_card_filter_not (s := S) (fun ℓ => ℓ.1 ≤ L)]
    congr 2
    ext ℓ
    simp only [A, S, Finset.mem_filter, Finset.mem_univ, true_and, mem_linesOf]
    exact and_comm
  have hYB : Y.card + B.card = A.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := A) (fun ℓ => ℓ.1 ≤ W.1)]
    congr 2
    ext ℓ
    simp only [A, Y, Finset.mem_filter, mem_linesOf, hW1, le_inf_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h1, h2⟩
    · rintro ⟨⟨h1, h3⟩, -, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have hYC : Y.card + C.card = θ := by
    rw [← hθW, ← Finset.card_filter_add_card_filter_not (s := linesOf W.1) (fun ℓ => c ℓ ≠ 0)]
  -- (i) `θ ≤ |A|`
  have hA : θ ≤ A.card := by
    have hfib := fiber_le R e (linesOf κ.1)
      (fun μ => (linesOf (Pl R e μ)).filter (fun ℓ => c ℓ ≠ 0)) A (by
        intro μ hμ ℓ hℓ
        simp only [Finset.mem_filter, mem_linesOf] at hℓ hμ
        have hℓR : ℓ ≠ R := fun h => hℓ.2 (h ▸ hR)
        refine ⟨hℓ.1, hℓR, ?_⟩
        simp only [A, Finset.mem_filter, mem_linesOf]
        refine ⟨?_, hℓ.2⟩
        rw [le_comap_iff R e ℓ hℓR, ← (le_P_iff_eq R e ℓ hℓR μ).mp hℓ.1]
        exact hμ)
    have h1 : ∀ μ ∈ linesOf κ.1,
        1 ≤ ((linesOf (Pl R e μ)).filter (fun ℓ => c ℓ ≠ 0)).card := by
      intro μ hμ
      rw [mem_linesOf] at hμ
      have h2 := congrFun hκ μ
      rw [proj_eq_sum, Pi.smul_apply, smul_eq_mul] at h2
      unfold incH at h2
      rw [if_pos hμ, mul_one] at h2
      obtain ⟨ℓ, hℓ, hℓ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h2 ▸ hσ0)
      exact Finset.card_pos.mpr ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, hℓ0⟩⟩
    have h2 := Finset.card_nsmul_le_sum _ _ 1 h1
    rw [smul_eq_mul, mul_one, card_linesOf] at h2
    have hκr : finrank K κ.1 = m - 2 := by have := κ.2; omega
    rw [hκr] at h2
    exact h2.trans hfib
  -- `p = 2`: no 2-secants, so (Lemma 5.7 twice) the support lies in a codimension-two `W`
  by_cases hp2 : p = 2
  · exfalso
    have h20 : ((2 : ℕ) : ZMod p) = 0 := by rw [ZMod.natCast_eq_zero_iff, hp2]
    have hline : ∀ s : Submodule K (Fin m → K), finrank K s = 2 →
        ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card ≤ 1 ∨
          Fintype.card K ≤ ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card := by
      intro s hs
      obtain ⟨h1, h2, -⟩ := secant hB p a hQ h49 h121 hK hm c hc hw s hs
      rw [hK]
      rcases h1 with h | h
      · by_cases h3 : ((linesOf s).filter (fun ℓ => c ℓ ≠ 0)).card = 2
        · exfalso
          have h4 := h2 h3
          rw [← hσ, ← Finset.sum_filter_ne_zero,
            Finset.sum_congr rfl (fun ℓ hℓ => hall ℓ (Finset.mem_filter.mp hℓ).2),
            Finset.sum_const, h3, nsmul_eq_mul, h20, zero_mul] at h4
          exact hσ0 h4.symm
        · left; omega
      · right; exact h
    have hbig : ∀ k, n + 2 ≤ k → hammingNorm c < Fintype.card K ^ k := by
      intro k hk
      have h1 : Fintype.card K ^ (n + 2) ≤ Fintype.card K ^ k :=
        Nat.pow_le_pow_right (by omega) hk
      have h4 : Fintype.card K ^ (n + 2) =
          (Fintype.card K ^ n * Fintype.card K) * Fintype.card K := by ring
      have h5 : (Fintype.card K ^ n * Fintype.card K) * 33 ≤
          (Fintype.card K ^ n * Fintype.card K) * Fintype.card K := Nat.mul_le_mul_left _ hQ33
      omega
    obtain ⟨H₁, -, hH₁r, hc₁⟩ := gen (by omega : 4 ≤ Fintype.card K) (m - 1)
      (fun ℓ => c ℓ ≠ 0) hline ⊤ (by rw [finrank_top, Module.finrank_fin_fun]; omega)
    have hH₁r' : finrank K H₁ = n + 3 := by
      rw [finrank_top, Module.finrank_fin_fun] at hH₁r; omega
    rcases hc₁ with hs₁ | hs₁
    swap
    · have := compl_count c ⊤ H₁ le_top hH₁r (fun ℓ _ h => hs₁ ℓ le_top h)
      rw [hH₁r'] at this
      exact absurd this (not_le.mpr (hbig _ (by omega)))
    obtain ⟨H₂, hH₂, hH₂r, hc₂⟩ := gen (by omega : 4 ≤ Fintype.card K) (m - 2)
      (fun ℓ => c ℓ ≠ 0) hline H₁ (by omega)
    have hH₂r' : finrank K H₂ = n + 2 := by omega
    rcases hc₂ with hs₂ | hs₂
    swap
    · have := compl_count c H₁ H₂ hH₂ hH₂r hs₂
      rw [hH₂r'] at this
      exact absurd this (not_le.mpr (hbig _ le_rfl))
    have hsupp : ∀ ℓ : Lines K m, c ℓ ≠ 0 → ℓ.1 ≤ H₂ :=
      fun ℓ h => hs₂ ℓ (hs₁ ℓ le_top h) h
    apply hobs
    refine ⟨⟨H₂, by omega⟩, σ, hσ0, ?_⟩
    show (linesOf H₂).card < 2 * ((linesOf H₂).filter (fun ℓ => c ℓ = σ)).card
    have hsub : A ⊆ (linesOf H₂).filter (fun ℓ => c ℓ = σ) := by
      intro ℓ hℓ
      simp only [A, Finset.mem_filter] at hℓ
      rw [Finset.mem_filter, mem_linesOf]
      exact ⟨hsupp ℓ hℓ.2, hall ℓ hℓ.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (linesOf H₂).card = θ := by
      rw [card_linesOf, hH₂r', hθ]; congr 1; omega
    have hθ1 : 1 ≤ θ := by
      rw [hθ, show m - 2 = (n + 1) + 1 by omega]
      have := th_ge (Fintype.card K) (n + 1) hq2
      have := Nat.one_le_pow (n + 1) (Fintype.card K) (by omega)
      omega
    omega
  -- `p` odd
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  -- (ii) the count through `R'`
  have hBL : ∀ P ∈ B ∪ C, P.1 ≤ L := by
    intro P hP
    simp only [B, C, A, Finset.mem_union, Finset.mem_filter, mem_linesOf, hW1] at hP
    rcases hP with h | h
    · exact h.1.1
    · exact h.1.trans inf_le_left
  have hfib := fiber_le2 R' L hR'L (B ∪ C) hBL
    (fun P => ((linesOf (R'.1 ⊔ P.1)).filter (fun ℓ => c ℓ ≠ 0)).filter
      (fun ℓ => ¬ ℓ.1 ≤ L)) D (by
      intro P _ ℓ hℓ
      simp only [Finset.mem_filter, mem_linesOf] at hℓ
      refine ⟨hℓ.1.1, fun h => hℓ.1.2 (h ▸ hR'), ?_⟩
      simp only [D, S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hℓ.1.2, hℓ.2⟩)
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro P h1 h2
    simp only [B, C, A, Finset.mem_filter] at h1 h2
    exact h2.2 h1.1.2
  rw [Finset.sum_union hBC] at hfib
  have hBsum : ∀ P ∈ B, Fintype.card K - 1 ≤
      (((linesOf (R'.1 ⊔ P.1)).filter (fun ℓ => c ℓ ≠ 0)).filter (fun ℓ => ¬ ℓ.1 ≤ L)).card := by
    intro P hP
    simp only [B, A, Finset.mem_filter, mem_linesOf, hW1, le_inf_iff] at hP
    obtain ⟨⟨hPL, hP0⟩, hPW⟩ := hP
    have hPL' : ¬ P.1 ≤ L' := fun h => hPW ⟨hPL, h⟩
    have hPR' : R' ≠ P := fun h => hR'L (h ▸ hPL)
    set G0 := (linesOf (R'.1 ⊔ P.1)).filter (fun ℓ => c ℓ ≠ 0) with hG0
    have hs := hsumP P hPL
    rw [if_neg hPL', ← Finset.sum_filter_ne_zero, ← hG0,
      Finset.sum_congr rfl (fun ℓ hℓ => hall ℓ (Finset.mem_filter.mp hℓ).2),
      Finset.sum_const, nsmul_eq_mul] at hs
    have hdvd : p ∣ G0.card := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact (mul_eq_zero.mp hs).resolve_right hσ0
    have hPG : P ∈ G0 := Finset.mem_filter.mpr ⟨(mem_linesOf _ _).mpr le_sup_right, hP0⟩
    have hG1 : 1 ≤ G0.card := Finset.card_pos.mpr ⟨P, hPG⟩
    have hGp : p ≤ G0.card := Nat.le_of_dvd hG1 hdvd
    have hsec := (secant hB p a hQ h49 h121 hK hm c hc hw (R'.1 ⊔ P.1)
      (finrank_join hPR')).1
    have hGQ : Fintype.card K ≤ G0.card := by
      rw [hK]; rcases hsec with h | h
      · have h' : G0.card ≤ 2 := by convert h
        omega
      · convert h
    have hin : (G0.filter (fun ℓ => ℓ.1 ≤ L)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      simp only [hG0, Finset.mem_filter, mem_linesOf] at hx hy
      exact line_eq_of_small (inf_small hR'L hPL) (le_inf hx.1.1 hx.2) (le_inf hy.1.1 hy.2)
    have := Finset.card_filter_add_card_filter_not (s := G0) (fun ℓ => ℓ.1 ≤ L)
    omega
  have hCsum : ∀ P ∈ C, 1 ≤
      (((linesOf (R'.1 ⊔ P.1)).filter (fun ℓ => c ℓ ≠ 0)).filter (fun ℓ => ¬ ℓ.1 ≤ L)).card := by
    intro P hP
    simp only [C, Finset.mem_filter, mem_linesOf, hW1, le_inf_iff, not_not] at hP
    obtain ⟨⟨hPL, hPL'⟩, hP0⟩ := hP
    have hs := hsumP P hPL
    rw [if_pos hPL'] at hs
    obtain ⟨ℓ, hℓ, hℓ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hs ▸ hσ0)
    rw [mem_linesOf] at hℓ
    have hℓL : ¬ ℓ.1 ≤ L := by
      intro h
      have := line_eq_of_small (inf_small hR'L hPL) (le_inf hℓ h) (le_inf le_sup_right hPL)
      exact hℓ0 (this ▸ hP0)
    exact Finset.card_pos.mpr ⟨ℓ, by simp [mem_linesOf, hℓ, hℓ0, hℓL]⟩
  have hB2 := Finset.card_nsmul_le_sum _ _ _ hBsum
  have hC2 := Finset.card_nsmul_le_sum _ _ _ hCsum
  rw [smul_eq_mul] at hB2 hC2
  -- the contradiction with Observation 1
  apply hobs
  refine ⟨W, σ, hσ0, ?_⟩
  have hfilt : (linesOf W.1).filter (fun ℓ => c ℓ = σ) = Y := by
    apply Finset.filter_congr
    intro ℓ _
    exact ⟨fun h => h ▸ hσ0, hall ℓ⟩
  rw [hfilt, hθW]
  have hθ1 : Fintype.card K ^ n * Fintype.card K ≤ θ := by
    rw [hθ, show m - 2 = (n + 1) + 1 by omega, ← pow_succ]
    exact th_ge _ _ hq2
  have h32 : B.card * 32 ≤ B.card * (Fintype.card K - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## AD21 Theorem 5.9 (case `n = k + 2`) -/

theorem chk_step (hB : BaseCase) (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) {m : ℕ} (hm : 4 ≤ m) :
    ∀ v ∈ Um K m p, hammingNorm v ≤ Lm (p ^ a) m →
      ∃ W W' : Codim2 K m, ∃ α β : ZMod p,
        v = α • incVec (ZMod p) W + β • incVec (ZMod p) W' := by
  suffices h : ∀ N : ℕ, ∀ v ∈ Um K m p, hammingNorm v = N → hammingNorm v ≤ Lm (p ^ a) m →
      ∃ W W' : Codim2 K m, ∃ α β : ZMod p,
        v = α • incVec (ZMod p) W + β • incVec (ZMod p) W' by
    intro v hv hw; exact h _ v hv rfl hw
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro v hv hN hw
  by_contra hnot
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨W⟩ := codim2_nonempty (K := K) (m := m) (by omega)
    exact hnot ⟨W, W, 0, 0, by simp⟩
  apply main hB p a hQ h49 h121 hK hm v hv hw hv0
  rintro ⟨W, α, hα, hlt⟩
  classical
  -- Observation 1: `v - α u_W` is lighter
  set A := (linesOf W.1).filter (fun ℓ => v ℓ = α) with hA
  set S := Finset.univ.filter (fun ℓ : Lines K m => v ℓ ≠ 0) with hS
  have hwt : hammingNorm v = S.card := rfl
  have hAS : A ⊆ S := by
    intro ℓ hℓ
    simp only [hA, hS, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
    rw [hℓ.2]; exact hα
  have hAW : A ⊆ linesOf W.1 := Finset.filter_subset _ _
  have hsub : Finset.univ.filter (fun ℓ => (v - α • incVec (ZMod p) W) ℓ ≠ 0) ⊆
      (S \ A) ∪ (linesOf W.1 \ A) := by
    intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at hℓ
    simp only [hA, hS, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
      true_and, mem_linesOf]
    by_cases hW : ℓ.1 ≤ W.1
    · have hi : incVec (ZMod p) W ℓ = 1 := by unfold incVec; rw [if_pos hW]
      rw [hi, mul_one] at hℓ
      right
      exact ⟨hW, fun h => hℓ (by rw [h.2, sub_self])⟩
    · have hi : incVec (ZMod p) W ℓ = 0 := by unfold incVec; rw [if_neg hW]
      rw [hi, mul_zero, sub_zero] at hℓ
      left
      exact ⟨hℓ, fun h => hW h.1⟩
  have hlt' : hammingNorm (v - α • incVec (ZMod p) W) < hammingNorm v := by
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_sdiff_of_subset hAS, Finset.card_sdiff_of_subset hAW] at h1
    have h2 := Finset.card_le_card hAS
    have h3 := Finset.card_le_card hAW
    have hn : hammingNorm (v - α • incVec (ZMod p) W) =
        (Finset.univ.filter (fun ℓ => (v - α • incVec (ZMod p) W) ℓ ≠ 0)).card := rfl
    rw [hn, hwt]
    omega
  have hmem : v - α • incVec (ZMod p) W ∈ Um K m p :=
    Submodule.sub_mem _ hv (Submodule.smul_mem _ α (Submodule.subset_span ⟨W, rfl⟩))
  obtain ⟨W₁, W₂, β₁, β₂, h12⟩ := ih _ (hN ▸ hlt') _ hmem rfl (hlt'.le.trans hw)
  have hveq : v = β₁ • incVec (ZMod p) W₁ + β₂ • incVec (ZMod p) W₂ + α • incVec (ZMod p) W := by
    rw [← h12]; abel
  by_cases h2 : ∃ X X' : Codim2 K m, ∃ γ δ : ZMod p,
      β₁ • incVec (ZMod p) W₁ + β₂ • incVec (ZMod p) W₂ + α • incVec (ZMod p) W =
        γ • incVec (ZMod p) X + δ • incVec (ZMod p) X'
  · obtain ⟨X, X', γ, δ, hX⟩ := h2
    exact hnot ⟨X, X', γ, δ, hveq.trans hX⟩
  · have := three_weight_gt hB p a hQ h49 h121 hK hm W₁ W₂ W β₁ β₂ α h2
    rw [← hveq] at this
    omega

end ProxGapTight.Dev.Q350.Step

namespace ProxGapTight.Dev.Q350
open ProxGapTight

theorem step : type_of% @Step.chk_step := @Step.chk_step

end ProxGapTight.Dev.Q350
end

section
set_option autoImplicit false

namespace ProxGapTight.Dev.Q350.Final
open ProxGapTight ProxGapTight.Dev.Q350

theorem incH_eq {K : Type} [Field K] {d p : ℕ} (H : Hyp K d) :
    incH (ZMod p) H = Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p)) := by
  classical
  funext ℓ
  simp [incH, Set.indicator]

theorem baseCase : BaseCase := by
  intro p a _ hQ h49 h121 d hd K _ _ hK v hv hw
  have hv' : v ∈ Submodule.span (ZMod p) (Set.range fun H :
        {H : Submodule K (Fin d → K) // Module.finrank K H + 1 = d} =>
          Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p))) := by
    have : (Set.range fun H : Hyp K d => incH (ZMod p) H) = (Set.range fun H :
        {H : Submodule K (Fin d → K) // Module.finrank K H + 1 = d} =>
          Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p))) := by
      ext f; simp only [Set.mem_range]
      constructor
      · rintro ⟨H, rfl⟩; exact ⟨H, (incH_eq H).symm⟩
      · rintro ⟨H, rfl⟩; exact ⟨H, incH_eq H⟩
    simpa [HypCode, this] using hv
  have hw' : hammingNorm v ≤ 3 * (p ^ a) ^ (d - 2) - 3 * (p ^ a) ^ (d - 3) - 1 := by
    have h1 : d + 1 - 3 = d - 2 := by omega
    have h2 : d + 1 - 4 = d - 3 := by omega
    simpa [Lm, h1, h2] using hw
  obtain ⟨H, H', α, β, h⟩ :=
    ad21_result_3_3_hyperplanes p a hQ h49 h121 d hd K hK v hv' hw'
  refine ⟨H, H', α, β, ?_⟩
  classical
  subst h
  funext ℓ
  simp [incH, Set.indicator]

theorem chk_theorem_3_3_small_weight (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = p ^ a →
      ∀ v ∈ Um K m p, hammingNorm v ≤ Lm (p ^ a) m →
        ∃ W W' : Codim2 K m, ∃ α β : ZMod p,
          v = α • incVec (ZMod p) W + β • incVec (ZMod p) W' := by
  refine ⟨4, fun m hm K _ _ hK => ?_⟩
  exact step baseCase p a hQ h49 h121 hK hm

end ProxGapTight.Dev.Q350.Final
end

theorem solution : type_of% @ProxGapTight.Dev.Q350.Final.chk_theorem_3_3_small_weight := @ProxGapTight.Dev.Q350.Final.chk_theorem_3_3_small_weight

-- Prove2me | solution 1 for PositivityTheory.ThKH.Iwas.group_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:35.682742+00:00
-- url     : https://prove2.me/submissions/150b1d0a-aa4d-4566-85d4-d22f84dfd004

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_IwasLoc
import Theorems.Thm_PositivityTheory_ThKH_Iwas_Wm_map
import Theorems.Thm_PositivityTheory_ThKH_Iwas_inv_apply_of_iso
import Theorems.Thm_PositivityTheory_ThKH_Iwas_exists_reduce
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_Wm_mul_self
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_decomp_split
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_iso_Wm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Iwas
open Matrix Formalism.UG Formalism.UG.P GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
namespace PositivityTheory.ThKH.Iwas
theorem _root_.solution {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {m : ℕ} {G : Type} [Group G] (U : Subgroup G)
    (Φ : G →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) (hiso : ∀ g, Iso c (Wm L (Fin m)) (Wm L (Fin m)) (Φ g))
    (inj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g')
    (surj : ∀ M, Iso c (Wm L (Fin m)) (Wm L (Fin m)) M → ∃ g ∈ U, Φ g = M) (K P : Set G)
    (hK : ∀ g, g ∈ K ↔ g ∈ U ∧ (∀ i j, Valued.v (Φ g i j) ≤ 1) ∧ ∀ i j, Valued.v (Φ g⁻¹ i j) ≤ 1)
    (hP : ∀ g ∈ U, (∀ i j, Φ g (Sum.inr i) (Sum.inl j) = 0) → g ∈ P) :
    (∀ h ∈ U, ∃ p ∈ P, ∃ k ∈ K, h = p * k) ∧
    ∀ χ : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, χ (k * k') = χ k * χ k') → (∀ k ∈ K, k ∈ P → χ k = 1) → ∀ k ∈ K, χ k = 1 := by
  obtain ⟨hc, hv, -, -, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hinv : ∀ g i j, Φ g⁻¹ i j = c (Φ g j.swap i.swap) := fun g =>
    inv_apply_of_iso hc (hiso g) (by rw [← map_mul, mul_inv_cancel, map_one])
  have hK' : ∀ g ∈ U, (∀ i j, Valued.v (Φ g i j) ≤ 1) → g ∈ K := fun g hg h =>
    (hK g).2 ⟨hg, h, fun i j => by rw [hinv, hv]; exact h _ _⟩
  refine ⟨fun h hh => ?_, fun χ hχ h1 k hk => ?_⟩
  · obtain ⟨k, hk1, hk2, hk3⟩ := exists_reduce hc hv _ (hiso h⁻¹)
    obtain ⟨g, hg, rfl⟩ := surj k hk1
    refine ⟨(g * h⁻¹)⁻¹, hP _ (inv_mem (mul_mem hg (inv_mem hh))) fun i j => ?_, g, hK' g hg hk2, by group⟩
    rw [hinv, map_mul]
    exact (congrArg c (hk3 j i)).trans (map_zero c)
  · let A : Subring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring.toSubring
    haveI : IsLocalRing A :=
      inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)
    have hA : ∀ z, z ∈ A ↔ Valued.v z ≤ 1 := fun _ => Iff.rfl
    let σ : A →+* A := c.restrict A A fun z hz => by rw [hA, hv]; exact hz
    have hσσ : ∀ z, σ (σ z) = z := fun z => Subtype.ext (hc z)
    have hx0 : c x - x ≠ 0 := by
      intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
    have hxi : (c x - x)⁻¹ ∈ A := by rw [hA, map_inv₀, hx1, inv_one]
    have hz : IsUnit (σ ⟨x, hx⟩ - σ (σ ⟨x, hx⟩)) := by
      rw [hσσ]
      exact IsUnit.of_mul_eq_one ⟨_, hxi⟩ (Subtype.ext (mul_inv_cancel₀ hx0))
    have hw : σ ⟨x, hx⟩ * ⟨_, hxi⟩ + σ (σ ⟨x, hx⟩ * ⟨_, hxi⟩) = 1 := Subtype.ext (by
      change c x * (c x - x)⁻¹ + c (c x * (c x - x)⁻¹) = 1
      rw [map_mul, map_inv₀, map_sub, hc, ← neg_sub (c x) x, inv_neg]
      field_simp
      ring)
    have hmap : ∀ N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A,
        Iso σ (Wm A (Fin m)) (Wm A (Fin m)) N ↔ Iso c (Wm L (Fin m)) (Wm L (Fin m)) (N.map A.subtype) := fun N => by
      unfold Iso
      rw [← Wm_map A.subtype, ← transpose_map]
      change _ ↔ _ * _ * (N.map σ).map A.subtype = _
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      exact (Matrix.map_injective A.subtype_injective).eq_iff.symm
    have lift : ∀ N, Iso σ (Wm A (Fin m)) (Wm A (Fin m)) N → ∃ g ∈ U, g ∈ K ∧ Φ g = N.map A.subtype := fun N hN => by
      obtain ⟨g, hg, e⟩ := surj _ ((hmap N).1 hN)
      exact ⟨g, hg, hK' g hg fun i j => by rw [e]; exact (N i j).2, e⟩
    obtain ⟨hkU, hk1, -⟩ := (hK k).1 hk
    let H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A := Matrix.of fun i j => ⟨_, hk1 i j⟩
    have eH : H.map A.subtype = Φ k := rfl
    obtain ⟨s, u, t, b, d, i1, i2, i3, -, e⟩ := decomp_split hσσ hw hz ((hmap H).2 (eH ▸ hiso k))
    obtain ⟨g1, u1, k1, e1⟩ := lift _ i1
    obtain ⟨g2, u2, k2, e2⟩ := lift _ i2
    obtain ⟨g3, u3, k3, e3⟩ := lift _ i3
    obtain ⟨w, uw, kw, ew⟩ := lift _ (iso_Wm (σ := σ) (β := Fin m))
    have hmul : ∀ g ∈ K, ∀ g' ∈ K, g * g' ∈ K := fun g hg g' hg' => by
      obtain ⟨a1, a2, -⟩ := (hK g).1 hg
      obtain ⟨b1, b2, -⟩ := (hK g').1 hg'
      refine hK' _ (mul_mem a1 b1) fun i j => ?_
      rw [map_mul, Matrix.mul_apply]
      exact A.sum_mem fun l _ => A.mul_mem (a2 _ _) (b2 _ _)
    have p1 : χ g1 = 1 := h1 _ k1 (hP _ u1 fun i j => by rw [e1]; rfl)
    have p2 : χ g2 = 1 := h1 _ k2 (hP _ u2 fun i j => by rw [e2]; rfl)
    have p3 : χ g3 = 1 := h1 _ k3 (hP _ u3 fun i j => by rw [e3]; rfl)
    have pw : χ w * χ w = 1 := by
      rw [← hχ w kw w kw]
      refine h1 _ (hmul _ kw _ kw) (hP _ (mul_mem uw uw) fun i j => ?_)
      rw [map_mul, ew, ← Matrix.map_mul, Wm_mul_self]
      simp
    have ek : k = g1 * (w * g2 * w) * g3 :=
      inj _ hkU _ (mul_mem (mul_mem u1 (mul_mem (mul_mem uw u2) uw)) u3) (by
        rw [← eH, e]
        simp only [map_mul, Matrix.map_mul, e1, e2, e3, ew])
    rw [ek, hχ _ (hmul _ k1 _ (hmul _ (hmul _ kw _ k2) _ kw)) _ k3, hχ _ k1 _ (hmul _ (hmul _ kw _ k2) _ kw),
      hχ _ (hmul _ kw _ k2) _ kw, hχ _ kw _ k2, p1, p2, p3, mul_one, mul_one, one_mul, pw]
end PositivityTheory.ThKH.Iwas

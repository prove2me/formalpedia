-- Prove2me | solution 1 for PositivityTheory.Sph.sb_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:35.848868+00:00
-- url     : https://prove2.me/submissions/4d2ca714-3b3d-457d-a49d-0682e93ce429

import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LatDefs
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_ExistsVBallSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PositivityTheory.Sph
open ValuativeRel Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private lemma isOpen_vle (r : k) (hr : r ≠ 0) : IsOpen {x : k | valuation k x ≤ valuation k r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 (valuation k r) (by simpa using hr), fun z hz => ?_⟩
  have h : z = (z - x) + x := by ring
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hz hx ⊢
  rw [h]
  exact (Valuation.map_add _ _ _).trans (max_le hz.le hx)
private lemma vBall_eq {m p : Type} (r : k) : (vBall r : Set (Matrix m p k)) =
    Set.pi Set.univ (fun _ : m => Set.pi Set.univ
      (fun _ : p => {x : k | valuation k x ≤ valuation k r})) := by
  ext Z
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
private lemma isOpen_vBall {m p : Type} [Finite m] [Finite p] (r : k) (hr : r ≠ 0) :
    IsOpen (vBall r : Set (Matrix m p k)) := by
  rw [vBall_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_vle r hr
private lemma zero_mem_vBall {m p : Type} (r : k) : (0 : Matrix m p k) ∈ vBall r := by
  intro i j; simp
private lemma add_mem_vBall {m p : Type} {r : k} {Y Z : Matrix m p k} (hY : Y ∈ vBall r)
    (hZ : Z ∈ vBall r) : Y + Z ∈ vBall r := by
  intro i j
  simp only [Matrix.add_apply]
  exact (Valuation.map_add _ _ _).trans (max_le (hY i j) (hZ i j))
private lemma neg_mem_vBall {m p : Type} {r : k} {Y : Matrix m p k} (hY : Y ∈ vBall r) :
    -Y ∈ vBall r := by
  intro i j
  simpa [Matrix.neg_apply, Valuation.map_neg] using hY i j
private lemma vBall_mono {m p : Type} {r s : k} (h : valuation k r ≤ valuation k s) :
    (vBall r : Set (Matrix m p k)) ⊆ vBall s :=
  fun _ hZ i j => (hZ i j).trans h
private lemma smul_mem_vBall {m p : Type} (t : k) {Z : Matrix m p k} (hZ : IntM Z) :
    t • Z ∈ vBall t := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
  have := (Valuation.mem_integer_iff _ _).1 (hZ i j)
  calc _ ≤ valuation k t * 1 := mul_le_mul' le_rfl this
    _ = _ := mul_one _
private lemma exists_large {ι : Type} (s : Finset ι) (y : ι → k) :
    ∃ r : k, r ≠ 0 ∧ ∀ i ∈ s, valuation k (y i) ≤ valuation k r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨r, hr, h⟩ := ih
    rcases le_total (valuation k (y a)) (valuation k r) with hle | hle
    · refine ⟨r, hr, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hle
      · exact h i hi
    · rcases eq_or_ne (y a) 0 with h0 | h0
      · refine ⟨r, hr, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · simp [h0]
        · exact h i hi
      · refine ⟨y a, h0, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact le_rfl
        · exact (h i hi).trans hle
private lemma exists_small {ι : Type} (s : Finset ι) (f : ι → k) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ t : k, t ≠ 0 ∧ t ∈ 𝒪[k] ∧ ∀ i ∈ s, valuation k t ≤ valuation k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, ht, htO, h⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have htO' := (Valuation.mem_integer_iff _ _).1 htO
    rcases le_total (valuation k t) (valuation k (f a)) with hle | hle
    · refine ⟨t, ht, htO, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hle
      · exact h i hi
    · refine ⟨f a, hf a (Finset.mem_insert_self _ _), (Valuation.mem_integer_iff _ _).2
        (hle.trans htO'), fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_rfl
      · exact hle.trans (h i hi)
private lemma scalar_basis : (𝓝 (0 : k)).HasBasis (fun r : k => r ≠ 0)
    (fun r => {x : k | valuation k x ≤ valuation k r}) := by
  refine (IsValuativeTopology.hasBasis_nhds_zero' k).to_hasBasis ?_ ?_
  · intro γ hγ
    obtain ⟨a, rfl⟩ := ValuativeRel.valuation_surjective γ
    obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have ha : a ≠ 0 := by simpa using hγ
    have hw : w ≠ 0 := by simpa using hw0
    refine ⟨a * w, mul_ne_zero ha hw, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, map_mul] at hx ⊢
    exact hx.trans_lt (mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hw1)
  · intro r hr
    exact ⟨valuation k r, by simpa using hr,
      fun x hx => show valuation k x ≤ valuation k r from le_of_lt hx⟩
private lemma exists_vBall_subset {m p : Type} {U : Set (Matrix m p k)}
    (hU : U ∈ 𝓝 (0 : Matrix m p k)) : ∃ r : k, r ≠ 0 ∧ vBall r ⊆ U := by
  have hb2 := ((scalar_basis (k := k)).pi_self (ι := p)).pi_self (ι := m)
  have h0 : 𝓝 (0 : Matrix m p k) = Filter.pi (fun _ : m => Filter.pi (fun _ : p => 𝓝 (0 : k))) := by
    change 𝓝 (0 : m → p → k) = _
    rw [nhds_pi]
    congr 1
    funext i
    rw [nhds_pi]
    rfl
  rw [h0] at hU
  obtain ⟨⟨J, ⟨I, r⟩⟩, ⟨-, -, hr⟩, hsub⟩ := hb2.mem_iff.1 hU
  exact ⟨r, hr, fun Z hZ => hsub fun i _ j _ => hZ i j⟩
end PositivityTheory.Sph
end
end

set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph
open ValuativeRel Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.Sph
theorem _root_.solution {m p : Type} [Fintype m] [Fintype p] {Φ : Matrix m p k → ℂ} (h1 : IsLocallyConstant Φ)
    (h2 : HasCompactSupport Φ) :
    ∃ t : k, t ≠ 0 ∧ t ∈ 𝒪[k] ∧ (∀ Y, Φ Y ≠ 0 → IntM (t • Y)) ∧ ∀ Y Z, IntM Z → Φ (Y + t • Z) = Φ Y := by
  classical
  have hKc : IsCompact (tsupport Φ) := h2
  haveI : Nonempty {s : k // s ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨s, hs0, hsK⟩ : ∃ s : k, s ≠ 0 ∧ tsupport Φ ⊆ vBall s := by
    obtain ⟨⟨s, hs⟩, h⟩ := hKc.elim_directed_cover (ι := {s : k // s ≠ 0})
      (fun s => (vBall s.1 : Set (Matrix m p k))) (fun s => isOpen_vBall s.1 s.2)
      (fun Y _ => by
        obtain ⟨r, hr, h⟩ := exists_large (Finset.univ : Finset (m × p)) (fun ij => Y ij.1 ij.2)
        exact Set.mem_iUnion.2 ⟨⟨r, hr⟩, fun i j => h (i, j) (Finset.mem_univ _)⟩)
      (fun a b => by
        rcases le_total (valuation k a.1) (valuation k b.1) with h | h
        · exact ⟨b, vBall_mono h, subset_rfl⟩
        · exact ⟨a, subset_rfl, vBall_mono h⟩)
    exact ⟨s, hs, h⟩
  have hloc : ∀ x : Matrix m p k, ∃ r : k, r ≠ 0 ∧ ∀ Z ∈ vBall r, Φ (x + Z) = Φ x := by
    intro x
    have hU : (fun Z => x + Z) ⁻¹' (Φ ⁻¹' {Φ x}) ∈ 𝓝 (0 : Matrix m p k) :=
      IsOpen.mem_nhds ((h1.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id))
        (by simp)
    obtain ⟨r, hr, hsub⟩ := exists_vBall_subset hU
    exact ⟨r, hr, fun Z hZ => hsub hZ⟩
  choose rr hrr0 hrr using hloc
  obtain ⟨S, -, hS⟩ := hKc.elim_nhds_subcover (fun x => (fun Y => Y - x) ⁻¹' vBall (rr x))
    (fun x _ => IsOpen.mem_nhds
      ((isOpen_vBall _ (hrr0 x)).preimage (continuous_id.sub continuous_const))
      (by simpa using zero_mem_vBall (m := m) (p := p) (rr x)))
  obtain ⟨t₁, ht₁0, -, ht₁⟩ := exists_small S rr (fun x _ => hrr0 x)
  have key : ∀ Y ∈ tsupport Φ, ∀ Z ∈ vBall t₁, Φ (Y + Z) = Φ Y := by
    intro Y hY Z hZ
    obtain ⟨x, hxS, hYx⟩ := Set.mem_iUnion₂.1 (hS hY)
    have hYx' : Y - x ∈ vBall (rr x) := hYx
    have hZ' : Z ∈ vBall (rr x) := vBall_mono (ht₁ x hxS) hZ
    have e1 : Φ Y = Φ x := by
      have := hrr x (Y - x) hYx'
      rwa [add_sub_cancel] at this
    have e2 : Φ (Y + Z) = Φ x := by
      have := hrr x (Y - x + Z) (add_mem_vBall hYx' hZ')
      rwa [show x + (Y - x + Z) = Y + Z by abel] at this
    rw [e1, e2]
  have hinv : ∀ Y, ∀ Z ∈ vBall t₁, Φ (Y + Z) = Φ Y := by
    intro Y Z hZ
    by_cases hY : Y ∈ tsupport Φ
    · exact key Y hY Z hZ
    by_cases hYZ : Y + Z ∈ tsupport Φ
    · have := key (Y + Z) hYZ (-Z) (neg_mem_vBall hZ)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYZ]
  obtain ⟨t, ht0, htO, ht⟩ := exists_small (Finset.univ : Finset (Fin 2)) ![t₁, s⁻¹]
    (fun i _ => by fin_cases i <;> simp [ht₁0, hs0])
  have ht1 : valuation k t ≤ valuation k t₁ := by simpa using ht 0 (Finset.mem_univ _)
  have hts : valuation k t ≤ valuation k s⁻¹ := by simpa using ht 1 (Finset.mem_univ _)
  refine ⟨t, ht0, htO, fun Y hY i j => ?_, fun Y Z hZ => hinv Y (t • Z) (vBall_mono ht1 (smul_mem_vBall t hZ))⟩
  have := hsK (subset_tsupport Φ hY) i j
  rw [Valuation.mem_integer_iff, Matrix.smul_apply, smul_eq_mul, map_mul]
  calc valuation k t * valuation k (Y i j) ≤ valuation k s⁻¹ * valuation k s := mul_le_mul' hts this
    _ = 1 := by rw [map_inv₀, inv_mul_cancel₀ (by simpa using hs0)]
end PositivityTheory.Sph

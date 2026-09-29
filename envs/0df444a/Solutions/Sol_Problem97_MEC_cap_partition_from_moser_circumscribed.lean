-- Prove2me | solution 1 for Problem97.MEC.cap_partition_from_moser_circumscribed
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:54.508451+00:00
-- url     : https://prove2.me/submissions/291b6a8b-4f92-415c-8cba-e3c6759d115b

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Cap.PartitionFromMEC:5800:12787. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Cap_PartitionFromMEC
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_Moser_Triangle

section Erdos9796CountingFragment_Erdos9796Proof_P97_Cap_PartitionFromMEC

open Problem97 Problem97.MEC

/- Fragment from Erdos9796Proof.P97.Cap.PartitionFromMEC; source SHA-256 cb2a5ce1101a74572ab57000424dc5f4df662f147fba1a7de73bfcf938646f93 -/


/-!
# Cap partition from a circumscribed Moser triangle

This file bridges the geometric `Problem97.MEC.MoserTriangle`
(produced by the Sylvester dichotomy) to the structural
`Problem97.MoserTriangle` and from there to a `Problem97.CapTriple`
with the strengthened `arc_membership` field.

We restrict to the **circumscribed branch** of the dichotomy
(`case_split = Or.inl _`), where the three MEC-boundary vertices are
pairwise distinct.  The diameter branch (`Or.inr _`) is not handled
here; downstream consumers branch on the dichotomy.

The cap construction is the natural closed-arc filter using the
chord-separation predicate `Problem97.OnArcOpposite`:
* `C1 := A.filter (fun v => OnArcOpposite v1 v2 v3 v)`
* `C2 := A.filter (fun v => OnArcOpposite v2 v3 v1 v)`
* `C3 := A.filter (fun v => OnArcOpposite v3 v1 v2 v)`

Moser-vertex memberships fall out of algebraic identities (e.g.
`signedArea2 v1 v3 v1 = 0`) and the noncollinearity of the Moser
triangle vertices.  The "opposite apex not in own cap" clauses
(`v1 ∉ C1`, etc.) use that `signedArea2 v1 v2 v3 ≠ 0`.

## The `hAGenericCapCount` hypothesis

The closed-cap convention via `OnArcOpposite` is *algebraic* and does
not by itself imply that every non-Moser `A`-vertex lies in exactly
one cap.  Geometric counterexamples (e.g. a point strictly inside the
Moser triangle gives `0` caps; a point in a corner region gives `2`
caps) show the count is in `{0, 1, 2, 3}` over the affine plane.  For
the closed-cap-partition identity `|C1| + |C2| + |C3| = |A| + 3` to
hold downstream, we need the count to be exactly `1` on non-Moser
vertices — a *geometric* fact about A-vertices being either on the
MEC arc opposite to one of the Moser vertices, or strictly outside
exactly one chord.

We expose this as an explicit hypothesis `hAGenericCapCount`, which
downstream consumers establish via MEC + ConvexIndep + circumscribed
case structure.

## Main declarations

* Algebraic identities for `signedArea2` (`signedArea2_self_*`).
* Lemmas `onArcOpposite_of_chord_endpoint_{left,right}` — Moser
  vertex endpoints lie on their adjacent caps.
* `Problem97.signedArea2_eq_zero_of_onArcOpposite_self` — apex lies
  on its own cap only if the area degenerates.
* `Problem97.MEC.MoserTriangle.toStructural` — project the
  circumscribed branch to a structural `Problem97.MoserTriangle`.
* `Problem97.MEC.cap_partition_from_moser_circumscribed` — the main
  cap-partition existence theorem.
* `Problem97.SurplusCapPacket` — Moser triangle (carried as a
  non-obtuse circumscribed MEC triangle plus the circumscribed
  case-split) + cap triple over its structural projection +
  designation of one cap as surplus (`|Ci| > 4`).  This is the
  MEC-aware packet that downstream U1 sub-lemmas consume.
* `Problem97.SurplusCapPacket.IsM44` — predicate saying the cap
  multiset is `(m, 4, 4)` with `m ≥ 5`, and the surplus cap is the
  long one.
-/

open scoped EuclideanGeometry
open Finset



/- ### Algebraic identities for `signedArea2` -/

/-- If the apex vertex coincides with the first chord endpoint, the
signed area vanishes. -/
lemma Problem97.signedArea2_eq_endpoint_left (vj vk : ℝ²) :
    signedArea2 vj vj vk = 0 := by
  unfold signedArea2
  ring

/-- If the apex vertex coincides with the second chord endpoint, the
signed area vanishes. -/
lemma Problem97.signedArea2_eq_endpoint_right (vj vk : ℝ²) :
    signedArea2 vk vj vk = 0 := by
  unfold signedArea2
  ring

/- ### `OnArcOpposite` for Moser vertices -/

/-- The first chord endpoint trivially lies on the closed arc
opposite (because its signed area against the chord is zero). -/
lemma Problem97.onArcOpposite_of_chord_endpoint_left (vi vj vk : ℝ²) :
    OnArcOpposite vi vj vk vj := by
  unfold OnArcOpposite
  rw [signedArea2_eq_endpoint_left]
  simp

/-- The second chord endpoint trivially lies on the closed arc
opposite. -/
lemma Problem97.onArcOpposite_of_chord_endpoint_right (vi vj vk : ℝ²) :
    OnArcOpposite vi vj vk vk := by
  unfold OnArcOpposite
  rw [signedArea2_eq_endpoint_right]
  simp

/-- Opposite-apex test: `OnArcOpposite vi vj vk vi` reduces to
`signedArea2 vi vj vk ^ 2 ≤ 0`, which forces `signedArea2 vi vj vk = 0`. -/
lemma Problem97.signedArea2_eq_zero_of_onArcOpposite_self
    {vi vj vk : ℝ²} (h : OnArcOpposite vi vj vk vi) :
    signedArea2 vi vj vk = 0 := by
  unfold OnArcOpposite at h
  -- h : signedArea2 vi vj vk * signedArea2 vi vj vk ≤ 0
  have hsq : signedArea2 vi vj vk * signedArea2 vi vj vk = 0 := by
    have hnn : 0 ≤ signedArea2 vi vj vk * signedArea2 vi vj vk :=
      mul_self_nonneg _
    linarith
  exact mul_self_eq_zero.mp hsq



/- ### Bridge: circumscribed `MEC.MoserTriangle` → structural `MoserTriangle` -/



/- ### Cap-partition existence theorem -/

open Classical in

theorem solution
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (MT : Problem97.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩)
    (hMoserNonDeg : Problem97.signedArea2 MT.v1 MT.v2 MT.v3 ≠ 0)
    (hAGenericCapCount : ∀ v ∈ A, v ≠ MT.v1 → v ≠ MT.v2 → v ≠ MT.v3 →
      (if Problem97.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0)
        + (if Problem97.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0)
        + (if Problem97.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0)
        = 1) :
    Nonempty (Problem97.CapTriple A (MT.toStructural hCircumscribed)) := by
  classical
  set M := MT.toStructural hCircumscribed with hM_def
  -- Cap definitions.
  set C1 := A.filter (fun v => Problem97.OnArcOpposite MT.v1 MT.v2 MT.v3 v)
    with hC1_def
  set C2 := A.filter (fun v => Problem97.OnArcOpposite MT.v2 MT.v3 MT.v1 v)
    with hC2_def
  set C3 := A.filter (fun v => Problem97.OnArcOpposite MT.v3 MT.v1 MT.v2 v)
    with hC3_def
  -- M.v1 = MT.v1, M.v2 = MT.v2, M.v3 = MT.v3 by `toStructural`.
  refine ⟨{
    C1 := C1
    C2 := C2
    C3 := C3
    C1_subset := Finset.filter_subset _ _
    C2_subset := Finset.filter_subset _ _
    C3_subset := Finset.filter_subset _ _
    v1_notin_C1 := ?_
    v2_mem_C1 := ?_
    v3_mem_C1 := ?_
    v1_mem_C2 := ?_
    v2_notin_C2 := ?_
    v3_mem_C2 := ?_
    v1_mem_C3 := ?_
    v2_mem_C3 := ?_
    v3_notin_C3 := ?_
    nonmoser_in_one := ?_
    arc_membership := ?_ }⟩
  -- v1 ∉ C1: would force signedArea2 v1 v2 v3 = 0.
  · intro hv1_in
    rw [hC1_def, Finset.mem_filter] at hv1_in
    obtain ⟨_, hv1_arc⟩ := hv1_in
    exact hMoserNonDeg
      (Problem97.signedArea2_eq_zero_of_onArcOpposite_self hv1_arc)
  -- v2 ∈ C1.
  · rw [hC1_def, Finset.mem_filter]
    exact ⟨MT.v2_mem,
      Problem97.onArcOpposite_of_chord_endpoint_left MT.v1 MT.v2 MT.v3⟩
  -- v3 ∈ C1.
  · rw [hC1_def, Finset.mem_filter]
    exact ⟨MT.v3_mem,
      Problem97.onArcOpposite_of_chord_endpoint_right MT.v1 MT.v2 MT.v3⟩
  -- v1 ∈ C2 (chord endpoints v3, v1; apex v1 = right endpoint).
  · rw [hC2_def, Finset.mem_filter]
    exact ⟨MT.v1_mem,
      Problem97.onArcOpposite_of_chord_endpoint_right MT.v2 MT.v3 MT.v1⟩
  -- v2 ∉ C2: would force signedArea2 v2 v3 v1 = 0; convert via cyclic sym.
  · intro hv2_in
    rw [hC2_def, Finset.mem_filter] at hv2_in
    obtain ⟨_, hv2_arc⟩ := hv2_in
    have hz := Problem97.signedArea2_eq_zero_of_onArcOpposite_self hv2_arc
    apply hMoserNonDeg
    have hcyc : Problem97.signedArea2 MT.v1 MT.v2 MT.v3
        = Problem97.signedArea2 MT.v2 MT.v3 MT.v1 := by
      unfold Problem97.signedArea2; ring
    rw [hcyc]; exact hz
  -- v3 ∈ C2.
  · rw [hC2_def, Finset.mem_filter]
    exact ⟨MT.v3_mem,
      Problem97.onArcOpposite_of_chord_endpoint_left MT.v2 MT.v3 MT.v1⟩
  -- v1 ∈ C3.
  · rw [hC3_def, Finset.mem_filter]
    exact ⟨MT.v1_mem,
      Problem97.onArcOpposite_of_chord_endpoint_left MT.v3 MT.v1 MT.v2⟩
  -- v2 ∈ C3.
  · rw [hC3_def, Finset.mem_filter]
    exact ⟨MT.v2_mem,
      Problem97.onArcOpposite_of_chord_endpoint_right MT.v3 MT.v1 MT.v2⟩
  -- v3 ∉ C3.
  · intro hv3_in
    rw [hC3_def, Finset.mem_filter] at hv3_in
    obtain ⟨_, hv3_arc⟩ := hv3_in
    have hz := Problem97.signedArea2_eq_zero_of_onArcOpposite_self hv3_arc
    apply hMoserNonDeg
    have hcyc : Problem97.signedArea2 MT.v1 MT.v2 MT.v3
        = Problem97.signedArea2 MT.v3 MT.v1 MT.v2 := by
      unfold Problem97.signedArea2; ring
    rw [hcyc]; exact hz
  -- nonmoser_in_one: directly from hAGenericCapCount, after translating
  -- "v ∈ Ci ↔ OnArcOpposite ... v" via mem_filter.
  · intro v hv hvnotin
    have hv_ne_v1 : v ≠ MT.v1 := by
      intro h; apply hvnotin
      change v ∈ ({M.v1, M.v2, M.v3} : Finset ℝ²)
      rw [h]
      exact Finset.mem_insert_self _ _
    have hv_ne_v2 : v ≠ MT.v2 := by
      intro h; apply hvnotin
      change v ∈ ({M.v1, M.v2, M.v3} : Finset ℝ²)
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hv_ne_v3 : v ≠ MT.v3 := by
      intro h; apply hvnotin
      change v ∈ ({M.v1, M.v2, M.v3} : Finset ℝ²)
      rw [h]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hcount := hAGenericCapCount v hv hv_ne_v1 hv_ne_v2 hv_ne_v3
    -- Translate `v ∈ Ci ↔ OnArcOpposite ... v`.
    have h1 : (v ∈ C1) ↔ Problem97.OnArcOpposite MT.v1 MT.v2 MT.v3 v := by
      rw [hC1_def, Finset.mem_filter]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    have h2 : (v ∈ C2) ↔ Problem97.OnArcOpposite MT.v2 MT.v3 MT.v1 v := by
      rw [hC2_def, Finset.mem_filter]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    have h3 : (v ∈ C3) ↔ Problem97.OnArcOpposite MT.v3 MT.v1 MT.v2 v := by
      rw [hC3_def, Finset.mem_filter]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    -- Use the Decidable propext for each iff to rewrite the indicator.
    have e1 : (if v ∈ C1 then (1 : ℕ) else 0)
        = (if Problem97.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0) := by
      by_cases hC : v ∈ C1
      · rw [if_pos hC, if_pos (h1.mp hC)]
      · rw [if_neg hC, if_neg (mt h1.mpr hC)]
    have e2 : (if v ∈ C2 then (1 : ℕ) else 0)
        = (if Problem97.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0) := by
      by_cases hC : v ∈ C2
      · rw [if_pos hC, if_pos (h2.mp hC)]
      · rw [if_neg hC, if_neg (mt h2.mpr hC)]
    have e3 : (if v ∈ C3 then (1 : ℕ) else 0)
        = (if Problem97.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0) := by
      by_cases hC : v ∈ C3
      · rw [if_pos hC, if_pos (h3.mp hC)]
      · rw [if_neg hC, if_neg (mt h3.mpr hC)]
    rw [e1, e2, e3]
    exact hcount
  -- arc_membership: trivially from filter definitions.
  · intro v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [hC1_def, Finset.mem_filter]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    · rw [hC2_def, Finset.mem_filter]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    · rw [hC3_def, Finset.mem_filter]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩



/- ### Surplus cap: cap of size `> 4` (MEC-aware packet) -/





variable {A : Finset ℝ²}

















/- ### `(m, 4, 4)` regime predicate -/

end Erdos9796CountingFragment_Erdos9796Proof_P97_Cap_PartitionFromMEC

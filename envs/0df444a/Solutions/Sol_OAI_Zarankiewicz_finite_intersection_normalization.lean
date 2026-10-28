-- Prove2me | solution 1 for OAI.Zarankiewicz.finite_intersection_normalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:20:53.496961+00:00
-- url     : https://prove2.me/submissions/830276f5-2a0d-4d6b-80c0-c527dec1369b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002
import Definitions.Def_OAIB3Zr003
import Theorems.Thm_OAI_Zarankiewicz_nonempty_polygonalExterior

section
-- module Solutions.OAIB3_Zar.Crossing_AffinePathHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem intervalLeft_strictMono : StrictMono intervalLeft := by
  intro s t hst
  change s.val/2 < t.val/2
  exact div_lt_div_of_pos_right hst (by norm_num)

theorem intervalRight_strictMono : StrictMono intervalRight := by
  intro s t hst
  change (1+s.val)/2 < (1+t.val)/2
  have hh : s.val < t.val := hst
  linarith

theorem intervalSegment_left (a b t : unitInterval) :
    intervalSegment (intervalLeft a) (intervalLeft b) t=intervalLeft (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*(a.val/2)+t.val*(b.val/2)=((1-t.val)*a.val+t.val*b.val)/2
  ring

theorem intervalSegment_right (a b t : unitInterval) :
    intervalSegment (intervalRight a) (intervalRight b) t=intervalRight (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*((1+a.val)/2)+t.val*((1+b.val)/2)=(1+((1-t.val)*a.val+t.val*b.val))/2
  ring

theorem path_trans_intervalLeft {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalLeft t)=γ t := by
  rw [← (γ.trans η).extend_extends' (intervalLeft t)]
  rw [Path.extend_trans_of_le_half γ η (show (intervalLeft t).val ≤ 1/2 by
    change t.val/2 ≤ 1/2
    linarith [t.property.2])]
  have he : 2*(intervalLeft t).val=t.val := by change 2*(t.val/2)=t.val; ring
  rw [he,γ.extend_extends']

theorem path_trans_intervalRight {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalRight t)=η t := by
  rw [← (γ.trans η).extend_extends' (intervalRight t)]
  rw [Path.extend_trans_of_half_le γ η (show 1/2 ≤ (intervalRight t).val by
    change 1/2 ≤ (1+t.val)/2
    linarith [t.property.1])]
  have he : 2*(intervalRight t).val-1=t.val := by change 2*((1+t.val)/2)-1=t.val; ring
  rw [he,η.extend_extends']

theorem intervalSegment_zero_one (t : unitInterval) : intervalSegment 0 1 t=t := by
  apply Subtype.ext
  change (1-t.val)*0+t.val*1=t.val
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε < f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨ε,hε,hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi := hf i (Finset.mem_insert_self i S)
    refine ⟨min (ε/2) (f i/2),lt_min (by linarith) (by linarith),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt (by have hh := hbound j hj; linarith)

theorem finite_node_separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hn : Function.Injective node) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → ε < |node i-node j| := by
  obtain ⟨ε,hε,hb⟩ := finite_positive_lower_bound
    (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2))
    (fun ij => |node ij.1-node ij.2|) (by
      intro ij hij
      exact abs_pos.mpr (sub_ne_zero.mpr (hn.ne (Finset.mem_filter.mp hij).2)))
  exact ⟨ε,hε,fun i j hij => hb (i,j) (by simpa using hij)⟩

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RoundDiskClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical Topology

theorem dist_le_of_mem_closedRoundDisk (z x : Plane) (r : ℝ) (hr : 0 ≤ r)
    (hx : x ∈ closedRoundDisk z r) : dist x z ≤ r := by
  change (x.1-z.1)^2+(x.2-z.2)^2 ≤ r^2 at hx
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff,abs_le,abs_le]
  have h₁ := sq_nonneg (x.1-z.1)
  have h₂ := sq_nonneg (x.2-z.2)
  constructor <;> constructor <;> nlinarith

theorem exists_round_disk_clearance {ι : Type*} [Fintype ι]
    (z : ι → Plane) (K : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (hz : ∀ i, z i ∉ K i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, Disjoint (closedRoundDisk (z i) r) (K i) := by
  have hex (i : ι) : ∃ ε : ℝ, 0 < ε ∧ Metric.ball (z i) ε ⊆ (K i)ᶜ :=
    Metric.mem_nhds_iff.mp ((hK i).isClosed.isOpen_compl.mem_nhds (hz i))
  choose radius hpos hclear using hex
  obtain ⟨r,hr,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  refine ⟨r,hr,?_⟩
  intro i
  apply Set.disjoint_left.mpr
  intro x hx hmem
  have hd := dist_le_of_mem_closedRoundDisk (z i) x r hr.le hx
  exact hclear i (hd.trans_lt (hbound i (Finset.mem_univ _))) hmem

theorem exists_disjoint_round_disks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (hz : Function.Injective z) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r) := by
  obtain ⟨δ,hδ,hgap⟩ := finite_positive_lower_bound
    (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2)) (fun ij => dist (z ij.1) (z ij.2)) (by
      intro ij hij
      exact dist_pos.mpr (hz.ne (Finset.mem_filter.mp hij).2))
  refine ⟨δ/3,by positivity,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h₁ := dist_le_of_mem_closedRoundDisk (z i) x (δ/3) (by positivity) hx
  have h₂ := dist_le_of_mem_closedRoundDisk (z j) x (δ/3) (by positivity) hy
  have htri := dist_triangle (z i) x (z j)
  rw [dist_comm (z i) x] at htri
  have hg := hgap (i,j) (by simpa using hij)
  linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_MarkedCurveDisks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closedRoundDisk_mono (z : Plane) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    closedRoundDisk z r ⊆ closedRoundDisk z s := by
  intro x hx
  change squaredLength (x-z) ≤ r^2 at hx
  change squaredLength (x-z) ≤ s^2
  nlinarith

theorem finite_curve_mark_isolation {E M : Type*} [Fintype E] [Fintype M] [DecidableEq M]
    (γ : E → unitInterval → Plane) (hγ : ∀ e, Continuous (γ e))
    (mark : M → Plane) (hm : Function.Injective mark)
    (O : E → M → Set unitInterval) (hO : ∀ e k, IsOpen (O e k))
    (hvisit : ∀ e k t, γ e t=mark k → t ∈ O e k) :
    ∃ r : ℝ, 0 < r ∧
      (∀ k l, k ≠ l → Disjoint (closedRoundDisk (mark k) r) (closedRoundDisk (mark l) r)) ∧
      (∀ e k t, γ e t ∈ closedRoundDisk (mark k) r → t ∈ O e k) := by
  let K : E × M → Set Plane := fun ek => γ ek.1 '' (O ek.1 ek.2)ᶜ
  have hK (ek : E × M) : IsCompact (K ek) :=
    (hO ek.1 ek.2).isClosed_compl.isCompact.image (hγ ek.1)
  have hnot (ek : E × M) : mark ek.2 ∉ K ek := by
    rintro ⟨t,ht,he⟩
    exact ht (hvisit ek.1 ek.2 t he)
  obtain ⟨ρ,hρ,hclear⟩ := exists_round_disk_clearance (fun ek : E × M => mark ek.2) K hK hnot
  obtain ⟨σ,hσ,hdisjoint⟩ := exists_disjoint_round_disks mark hm
  refine ⟨min ρ σ,lt_min hρ hσ,?_,?_⟩
  · intro k l hkl
    exact (hdisjoint k l hkl).mono
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
  · intro e k t ht
    by_contra hn
    have hd : γ e t ∈ closedRoundDisk (mark k) ρ :=
      closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_left _ _) ht
    exact Set.disjoint_left.mp (hclear (e,k)) hd ⟨t,hn,rfl⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ParameterNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem parameterNeighborhood_open (t : unitInterval) (δ : ℝ) :
    IsOpen (parameterNeighborhood t δ) := by
  apply isOpen_lt _ continuous_const
  fun_prop

theorem parameterNeighborhood_between (t : unitInterval) (δ : ℝ)
    (u v w : unitInterval) (hu : u ∈ parameterNeighborhood t δ)
    (hv : v ∈ parameterNeighborhood t δ) (huw : u ≤ w) (hwv : w ≤ v) :
    w ∈ parameterNeighborhood t δ := by
  change |w.val-t.val| < δ
  change |u.val-t.val| < δ at hu
  change |v.val-t.val| < δ at hv
  rw [abs_lt] at hu hv ⊢
  have h₁ : u.val ≤ w.val := huw
  have h₂ : w.val ≤ v.val := hwv
  constructor <;> linarith

theorem parameterNeighborhood_ordered (a b : unitInterval) (δ : ℝ) (hδ : 0 < δ)
    (hab : a < b) (hd : Disjoint (parameterNeighborhood a δ) (parameterNeighborhood b δ))
    (u v : unitInterval) (hu : u ∈ parameterNeighborhood a δ)
    (hv : v ∈ parameterNeighborhood b δ) : u < v := by
  by_contra hn
  have hvu : v ≤ u := le_of_not_gt hn
  have ha : a ∈ parameterNeighborhood a δ := by simpa [parameterNeighborhood] using hδ
  have hb : b ∈ parameterNeighborhood b δ := by simpa [parameterNeighborhood] using hδ
  by_cases hva : v ≤ a
  · exact Set.disjoint_left.mp hd ha (parameterNeighborhood_between b δ v b a hv hb hva hab.le)
  · have hav : a ≤ v := (lt_of_not_ge hva).le
    exact Set.disjoint_left.mp hd (parameterNeighborhood_between a δ a u v ha hu hav hvu) hv

theorem finite_parameter_neighborhoods {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → unitInterval) (ht : Function.Injective t) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, t i ∈ parameterNeighborhood (t i) δ) ∧
      (∀ i j, i ≠ j → Disjoint (closure (parameterNeighborhood (t i) δ))
        (closure (parameterNeighborhood (t j) δ))) := by
  obtain ⟨ε,hε,hsep⟩ := finite_node_separation (fun i => (t i).val)
    (Subtype.val_injective.comp ht)
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hclosed (i : ι) : IsClosed {s : unitInterval | |s.val-(t i).val| ≤ δ} := by
    apply isClosed_le _ continuous_const
    fun_prop
  have hcl (i : ι) : closure (parameterNeighborhood (t i) δ) ⊆
      {s : unitInterval | |s.val-(t i).val| ≤ δ} :=
    closure_minimal (fun s hh => le_of_lt (show |s.val-(t i).val| < δ from hh)) (hclosed i)
  refine ⟨δ,hδ,fun i => by simpa [parameterNeighborhood] using hδ,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := hcl i hx
  have hy' := hcl j hy
  have hg := hsep i j hij
  have htri := abs_sub_le (t i).val x.val (t j).val
  rw [abs_sub_comm (t i).val x.val] at htri
  change |x.val-(t i).val| ≤ δ at hx'
  change |x.val-(t j).val| ≤ δ at hy'
  dsimp [δ] at hx' hy'
  linarith

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CurveDiskIsolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_injective_curve_disk_isolation {E M : Type*}
    [Fintype E] [Fintype M] [DecidableEq M]
    (γ : E → unitInterval → Plane) (hc : ∀ e, Continuous (γ e))
    (hi : ∀ e, Function.Injective (γ e)) (mark : M → Plane) (hm : Function.Injective mark) :
    ∃ δ : E → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ k l, k ≠ l → Disjoint (closedRoundDisk (mark k) r) (closedRoundDisk (mark l) r)) ∧
      (∀ e k t, γ e t ∈ closedRoundDisk (mark k) r →
        ∃ u : unitInterval, γ e u=mark k ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, γ e u ∈ Set.range mark → γ e v ∈ Set.range mark → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  have hfinite (e : E) : ((γ e) ⁻¹' Set.range mark).Finite :=
    Set.Finite.preimage (hi e).injOn (Set.finite_range mark)
  have hex (e : E) : ∃ δ : ℝ, 0 < δ ∧
      ∀ u v, γ e u ∈ Set.range mark → γ e v ∈ Set.range mark → u ≠ v →
        Disjoint (closure (parameterNeighborhood u δ)) (closure (parameterNeighborhood v δ)) := by
    let S := (γ e) ⁻¹' Set.range mark
    let : Fintype S := (hfinite e).fintype
    let : DecidableEq S := Classical.decEq _
    obtain ⟨δ,hδ,_,hd⟩ := finite_parameter_neighborhoods (fun t : S => t.val) Subtype.val_injective
    refine ⟨δ,hδ,?_⟩
    intro u v hu hv huv
    exact hd ⟨u,hu⟩ ⟨v,hv⟩ (fun he => huv (congrArg Subtype.val he))
  choose δ hδ hseparate using hex
  let O : E → M → Set unitInterval := fun e k =>
    {t | ∃ u, γ e u=mark k ∧ t ∈ parameterNeighborhood u (δ e)}
  have hO (e : E) (k : M) : IsOpen (O e k) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro t ⟨u,hu,ht⟩
    exact Filter.mem_of_superset ((parameterNeighborhood_open u (δ e)).mem_nhds ht)
      (fun s hs => ⟨u,hu,hs⟩)
  obtain ⟨r,hr,hdisks,hvisits⟩ := finite_curve_mark_isolation γ hc mark hm O hO (by
    intro e k t ht
    exact ⟨t,ht,by simpa [parameterNeighborhood] using hδ e⟩)
  exact ⟨δ,r,hδ,hr,hdisks,hvisits,hseparate⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingMarks
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem drawingMarks_finite (D : FiniteIntersectionDrawing m n) : (drawingMarks D).Finite :=
  (Set.finite_range D.vertex).union D.crossings_finite

theorem marked_parameters_finite (D : FiniteIntersectionDrawing m n) (e : BipartiteEdge m n) :
    ((D.edge e) ⁻¹' drawingMarks D).Finite :=
  Set.Finite.preimage (D.edge_injective e).injOn (drawingMarks_finite D)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingDiskIsolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem drawing_disk_isolation (D : FiniteIntersectionDrawing m n) :
    ∃ δ : BipartiteEdge m n → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ x y : DrawingMark D, x ≠ y →
        Disjoint (closedRoundDisk x.val r) (closedRoundDisk y.val r)) ∧
      (∀ e (x : DrawingMark D) t, D.edge e t ∈ closedRoundDisk x.val r →
        ∃ u : unitInterval, D.edge e u=x.val ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, D.edge e u ∈ drawingMarks D → D.edge e v ∈ drawingMarks D → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  let : DecidableEq (DrawingMark D) := Classical.decEq _
  obtain ⟨δ,r,hδ,hr,hd,hv,hs⟩ := finite_injective_curve_disk_isolation
    (fun e => D.edge e) (fun e => (D.edge e).continuous) D.edge_injective
    (fun x : DrawingMark D => x.val) Subtype.val_injective
  refine ⟨δ,r,hδ,hr,hd,hv,?_⟩
  intro e u v hu hv huv
  exact hs e u v ⟨⟨D.edge e u,hu⟩,rfl⟩ ⟨⟨D.edge e v,hv⟩,rfl⟩ huv

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_RoundDiskVisits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem continuous_path_squared_distance {a b : Plane} (γ : Path a b) (z : Plane) :
    Continuous (fun t : ℝ => squaredLength (γ.extend t-z)) := by
  unfold squaredLength
  fun_prop

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SublevelExtrema
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem sublevel_passage_extrema (f : ℝ → ℝ) (hf : Continuous f) (r τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hvisit : f τ < r) :
    ∃ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 ∧
      a ≤ τ ∧ τ ≤ b ∧ f a ≤ r ∧ f b ≤ r ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ r → a ≤ t ∧ t ≤ b) ∧
      (0 < a → f a=r) ∧ (b < 1 → f b=r) ∧
      (0 < τ → a < τ) ∧ (τ < 1 → τ < b) := by
  let S : Set ℝ := Set.Icc 0 1 ∩ {t | f t ≤ r}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hτS : τ ∈ S := ⟨hτ,hvisit.le⟩
  obtain ⟨a,ha⟩ := hS.exists_isLeast ⟨τ,hτS⟩
  obtain ⟨b,hb⟩ := hS.exists_isGreatest ⟨τ,hτS⟩
  have hfa (ha0 : 0 < a) : f a=r := by
    have hf0 : r < f 0 := by
      apply lt_of_not_ge
      intro h
      have hh := ha.2 (show (0 : ℝ) ∈ S from ⟨⟨le_rfl,zero_le_one⟩,h⟩)
      linarith
    apply le_antisymm ha.1.2
    by_contra hn
    have hlt : f a < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' ha.1.1.1 hf.continuousOn ⟨hlt.le,hf0.le⟩
    have hmem : t ∈ S := ⟨⟨ht.1,ht.2.trans ha.1.1.2⟩,he.le⟩
    have hta : t=a := le_antisymm ht.2 (ha.2 hmem)
    rw [hta] at he
    exact hlt.ne he
  have hfb (hb1 : b < 1) : f b=r := by
    have hf1 : r < f 1 := by
      apply lt_of_not_ge
      intro h
      have hh := hb.2 (show (1 : ℝ) ∈ S from ⟨⟨zero_le_one,le_rfl⟩,h⟩)
      linarith
    apply le_antisymm hb.1.2
    by_contra hn
    have hlt : f b < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hb.1.1.2 hf.continuousOn ⟨hlt.le,hf1.le⟩
    have hmem : t ∈ S := ⟨⟨hb.1.1.1.trans ht.1,ht.2⟩,he.le⟩
    have htb : t=b := le_antisymm (hb.2 hmem) ht.1
    rw [htb] at he
    exact hlt.ne he
  refine ⟨a,b,ha.1.1,hb.1.1,ha.2 hτS,hb.2 hτS,ha.1.2,hb.1.2,
    fun t ht hh => ⟨ha.2 ⟨ht,hh⟩,hb.2 ⟨ht,hh⟩⟩,hfa,hfb,?_,?_⟩
  · intro ht0
    apply lt_of_le_of_ne (ha.2 hτS)
    intro he
    have h := hfa (he.symm ▸ ht0)
    rw [he] at h
    exact hvisit.ne h
  · intro ht1
    apply lt_of_le_of_ne (hb.2 hτS)
    intro he
    have h := hfb (he ▸ ht1)
    rw [← he] at h
    exact hvisit.ne h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DiskPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem nonempty_diskPassage {a b : Plane} (γ : Path a b) (z : Plane) (r : ℝ)
    (τ : unitInterval) (hτ : squaredLength (γ τ-z) < r^2) :
    Nonempty (DiskPassage γ z r τ) := by
  obtain ⟨u,v,hu,hv,huτ,hτv,hfu,hfv,hall,hbu,hbv,hsu,hsv⟩ := sublevel_passage_extrema
    (fun t => squaredLength (γ.extend t-z)) (continuous_path_squared_distance γ z) (r^2) τ.val τ.property
    (by simpa using hτ)
  let u' : unitInterval := ⟨u,hu⟩
  let v' : unitInterval := ⟨v,hv⟩
  have heu : γ.extend u=γ u' := γ.extend_extends' u'
  have hev : γ.extend v=γ v' := γ.extend_extends' v'
  rw [heu] at hfu hbu
  rw [hev] at hfv hbv
  exact ⟨{
    enter := u'
    leave := v'
    enter_le_mark := huτ
    mark_le_leave := hτv
    enter_mem := hfu
    leave_mem := hfv
    all_visits := fun t ht => hall t.val t.property (by simpa [closedRoundDisk] using ht)
    enter_boundary := hbu
    leave_boundary := hbv
    strict_enter := hsu
    strict_leave := hsv }⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrderedPassages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem diskPassage_separated {a b z w : Plane} {γ : Path a b} {r δ : ℝ}
    {s t : unitInterval} (P : DiskPassage γ z r s) (Q : DiskPassage γ w r t)
    (hst : s < t) (hδ : 0 < δ)
    (hd : Disjoint (closure (parameterNeighborhood s δ)) (closure (parameterNeighborhood t δ)))
    (hP : P.leave ∈ parameterNeighborhood s δ) (hQ : Q.enter ∈ parameterNeighborhood t δ) :
    P.leave < Q.enter :=
  parameterNeighborhood_ordered s t δ hδ hst (hd.mono subset_closure subset_closure) P.leave Q.enter hP hQ

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SortedMarkedParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_sorted_unitInterval_finset (S : Finset unitInterval)
    (h0 : (0 : unitInterval) ∈ S) (h1 : (1 : unitInterval) ∈ S) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧ Set.range t=(S : Set unitInterval) := by
  have hc : 1 < S.card := Finset.one_lt_card.mpr ⟨0,h0,1,h1,zero_ne_one⟩
  let k := S.card-1
  have hk : 0 < k := by dsimp [k]; omega
  have hcard : S.card=k+1 := by dsimp [k]; omega
  let e := S.orderEmbOfFin hcard
  have hrange : Set.range e=(S : Set unitInterval) := Finset.range_orderEmbOfFin S hcard
  obtain ⟨i,hi⟩ : ∃ i, e i=0 := by
    have hm : (0 : unitInterval) ∈ Set.range e := hrange.symm ▸ h0
    exact hm
  obtain ⟨j,hj⟩ : ∃ j, e j=1 := by
    have hm : (1 : unitInterval) ∈ Set.range e := hrange.symm ▸ h1
    exact hm
  have he0 : e 0=0 := by
    apply le_antisymm
    · exact (e.monotone (Fin.zero_le i)).trans_eq hi
    · exact (e 0).property.1
  have he1 : e (Fin.last k)=1 := by
    apply le_antisymm
    · exact (e (Fin.last k)).property.2
    · exact hj.symm.trans_le (e.monotone (Fin.le_last j))
  exact ⟨k,hk,e,e.strictMono,he0,he1,hrange⟩

theorem exists_sorted_drawing_parameters {m n : ℕ} (D : FiniteIntersectionDrawing m n)
    (e : BipartiteEdge m n) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧
      Set.range t=(D.edge e) ⁻¹' drawingMarks D := by
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset (marked_parameters_finite D e).toFinset
    (by simpa using marked_parameter_zero D e) (by simpa using marked_parameter_one D e)
  exact ⟨k,hk,t,ht,h0,h1,by simpa using hR⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingPassages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem nonempty_drawingPassages (D : FiniteIntersectionDrawing m n) : Nonempty (DrawingPassages D) := by
  classical
  obtain ⟨δ,r,hδ,hr,hdisks,hvisits,hparam⟩ := drawing_disk_isolation D
  choose k hk τ hτ h0 h1 hR using (fun e => exists_sorted_drawing_parameters D e)
  have hnode (e : BipartiteEdge m n) (i : Fin (k e+1)) : D.edge e (τ e i) ∈ drawingMarks D := by
    change τ e i ∈ (D.edge e) ⁻¹' drawingMarks D
    rw [← hR e]
    exact ⟨i,rfl⟩
  have hex (e : BipartiteEdge m n) (i : Fin (k e+1)) :
      Nonempty (DiskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)) :=
    nonempty_diskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)
      (by simpa [squaredLength] using sq_pos_of_pos hr)
  let P (e : BipartiteEdge m n) (i : Fin (k e+1)) := Classical.choice (hex e i)
  have hlocal (e : BipartiteEdge m n) (i : Fin (k e+1)) (t : unitInterval)
      (ht : D.edge e t ∈ closedRoundDisk (D.edge e (τ e i)) r) :
      t ∈ parameterNeighborhood (τ e i) (δ e) := by
    obtain ⟨u,hu,hh⟩ := hvisits e ⟨D.edge e (τ e i),hnode e i⟩ t ht
    have he : u=τ e i := D.edge_injective e hu
    simpa [he] using hh
  have hsep (e : BipartiteEdge m n) (i j : Fin (k e+1)) (hij : i < j) :
      (P e i).leave < (P e j).enter := by
    apply diskPassage_separated (P e i) (P e j) (hτ e hij) (hδ e)
    · exact hparam e (τ e i) (τ e j) (hnode e i) (hnode e j) ((hτ e).injective.ne (ne_of_lt hij))
    · exact hlocal e i _ (P e i).leave_mem
    · exact hlocal e j _ (P e j).enter_mem
  exact ⟨{
    radius := r
    radius_pos := hr
    disks_disjoint := hdisks
    count := k
    count_pos := hk
    node := τ
    increasing := hτ
    first := h0
    last := h1
    node_range := hR
    passage := P
    separated := hsep
    visited_mark_on_edge := fun e x t ht => by
      obtain ⟨u,hu,_⟩ := hvisits e x t ht
      exact ⟨u,hu⟩ }⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteLineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators Classical

theorem lineAvoidancePolynomial_eval (z a v : Plane) (t : ℝ) :
    (lineAvoidancePolynomial z a v).eval t = det2 (z+(t,t^2)-a) v := by
  simp [lineAvoidancePolynomial,det2]
  ring

theorem lineAvoidancePolynomial_ne_zero (z a v : Plane) (hv : v ≠ 0) :
    lineAvoidancePolynomial z a v ≠ 0 := by
  intro h
  have h₁ := congrArg (fun p : ℝ[X] => p.coeff 1) h
  have h₂ := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [lineAvoidancePolynomial,coeff_C_mul] at h₁ h₂
  apply hv
  exact Prod.ext h₂ h₁

theorem exists_near_avoiding_lines {ι : Type*} [Fintype ι] (a v : ι → Plane)
    (hv : ∀ i, v i ≠ 0) (z : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ o : Plane, dist o z < ε ∧ ∀ i, det2 (o-a i) (v i) ≠ 0 := by
  let bad : Finset ℝ := Finset.univ.biUnion (fun i => (lineAvoidancePolynomial z (a i) (v i)).roots.toFinset)
  have hδ : 0 < min ε 1 := lt_min hε (by norm_num)
  obtain ⟨t,ht⟩ := ((Set.Ioo_infinite hδ).sdiff bad.finite_toSet).nonempty
  have ht0 : 0 < t := ht.1.1
  have htε : t < ε := lt_of_lt_of_le ht.1.2 (min_le_left _ _)
  have ht1 : t < 1 := lt_of_lt_of_le ht.1.2 (min_le_right _ _)
  refine ⟨z+(t,t^2),?_,?_⟩
  · have ht2 : t^2 < ε := by nlinarith
    simp only [Prod.dist_eq,Prod.fst_add,Prod.snd_add,Real.dist_eq,add_sub_cancel_left]
    exact max_lt (by simpa [abs_of_pos ht0] using htε) (by simpa [abs_of_nonneg (sq_nonneg t)] using ht2)
  · intro i hi
    have hp : (lineAvoidancePolynomial z (a i) (v i)).eval t = 0 := by
      rwa [lineAvoidancePolynomial_eval]
    apply ht.2
    change t ∈ bad
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ i,?_⟩
    simpa [mem_roots (lineAvoidancePolynomial_ne_zero z (a i) (v i) (hv i))] using hp

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_VertexDiskSpokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_vertex_disk_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Plane) (r : ℝ) (hr : 0 < r) (p : ι → Plane) (hp : Function.Injective p)
    (hcircle : ∀ i, squaredLength (p i-z)=r^2) :
    ∃ v : Plane, squaredLength (v-z) < r^2 ∧
      (∀ i, v ≠ p i) ∧ (∀ i j, i ≠ j → det2 (p i-v) (p j-v) ≠ 0) := by
  classical
  let S := {ij : ι × ι // ij.1 ≠ ij.2}
  obtain ⟨v,hv,havoid⟩ := exists_near_avoiding_lines
    (fun ij : S => p ij.val.1) (fun ij : S => p ij.val.2-p ij.val.1)
    (fun ij => sub_ne_zero.mpr (hp.ne (Ne.symm ij.property))) z (r/3) (by positivity)
  have hinside : squaredLength (v-z) < r^2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff,abs_lt,abs_lt] at hv
    have h₁ := mul_pos (sub_pos.mpr hv.1.2) (show 0 < r/3+(v.1-z.1) by linarith [hv.1.1])
    have h₂ := mul_pos (sub_pos.mpr hv.2.2) (show 0 < r/3+(v.2-z.2) by linarith [hv.2.1])
    change (v.1-z.1)^2+(v.2-z.2)^2 < r^2
    nlinarith [sq_pos_of_pos hr]
  refine ⟨v,hinside,?_,?_⟩
  · intro i he
    rw [he,hcircle i] at hinside
    exact lt_irrefl _ hinside
  · intro i j hij
    have he : det2 (p i-v) (p j-v) = -det2 (v-p i) (p j-p i) := by dsimp [det2]; ring
    rw [he]
    exact neg_ne_zero.mpr (havoid ⟨(i,j),hij⟩)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingVertexPlacement
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem exists_drawing_vertex_placement (C : DrawingPassages D) :
    ∃ v : BipartiteVertex m n → Plane, Function.Injective v ∧
      (∀ i, squaredLength (v i-D.vertex i) < C.radius^2) ∧
      (∀ i (p : C.PortsAt (C.vertexMark i)), v i ≠ C.portPoint p.val) ∧
      (∀ i (p q : C.PortsAt (C.vertexMark i)), p ≠ q →
        det2 (C.portPoint p.val-v i) (C.portPoint q.val-v i) ≠ 0) := by
  classical
  have hex (i : BipartiteVertex m n) : ∃ v : Plane,
      squaredLength (v-D.vertex i) < C.radius^2 ∧
      (∀ p : C.PortsAt (C.vertexMark i), v ≠ C.portPoint p.val) ∧
      (∀ p q : C.PortsAt (C.vertexMark i), p ≠ q → det2 (C.portPoint p.val-v) (C.portPoint q.val-v) ≠ 0) :=
    exists_vertex_disk_point (D.vertex i) C.radius C.radius_pos
      (fun p : C.PortsAt (C.vertexMark i) => C.portPoint p.val)
      (C.portPoint_injective.comp Subtype.val_injective) (C.portsAt_on_circle (C.vertexMark i))
  choose v hv hne hdet using hex
  refine ⟨v,?_,hv,hne,hdet⟩
  intro i j he
  by_contra hij
  have hd := C.disks_disjoint (C.vertexMark i) (C.vertexMark j) (C.vertexMark_injective.ne hij)
  have hi : v i ∈ closedRoundDisk (C.vertexMark i).val C.radius := (hv i).le
  have hj : v j ∈ closedRoundDisk (C.vertexMark j).val C.radius := (hv j).le
  exact Set.disjoint_left.mp hd hi (he.symm ▸ hj)

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingDiskCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
open scoped Classical
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem chordCrossings_ncard_le (C : DrawingPassages D) :
    C.chordCrossings.ncard ≤ finiteCrossingCount D := by
  calc
    C.chordCrossings.ncard ≤ (crossingPoints D.toContinuousDrawing).ncard :=
      Set.ncard_le_ncard_of_injOn C.chordCrossingOrigin C.chordCrossingOrigin_mapsTo
        C.chordCrossingOrigin_injOn D.crossings_finite
    _ = finiteCrossingCount D := Set.ncard_eq_toFinset_card _ D.crossings_finite

end Zarankiewicz.DrawingPassages

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AssembledAdmissibleDrawing
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_crossingCount_le (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    crossingCount (E.assembledAdmissible v hvinj hv hdet) ≤ finiteCrossingCount D := by
  have h := Set.ncard_le_ncard (E.assembled_crossings_subset v hvinj hv hdet) C.chordCrossings_finite
  have hcount : crossingCount (E.assembledAdmissible v hvinj hv hdet)=
      (crossingPoints (E.assembledDrawing v hvinj hv)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (E.assembled_crossings_finite v hvinj hv hdet)]
    rfl
  rw [hcount]
  exact h.trans C.chordCrossings_ncard_le

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_FiniteAffineCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem hasFiniteAffineCover_refl (a : Plane) : HasFiniteAffineCover (Path.refl a) := by
  classical
  refine ⟨{(0,1)},?_,?_,?_⟩
  · intro ab hab
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  · intro t
    exact ⟨(0,1),Finset.mem_singleton_self _,t.property.1,t.property.2⟩
  · intro ab hab t
    change a=segmentPoint a a t.val
    simp [segmentPoint,← add_smul]

theorem hasFiniteAffineCover_segment (a b : Plane) : HasFiniteAffineCover (Path.segment a b) := by
  classical
  refine ⟨{(0,1)},?_,?_,?_⟩
  · intro ab hab
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  · intro t
    exact ⟨(0,1),Finset.mem_singleton_self _,t.property.1,t.property.2⟩
  · intro ab hab t
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    simp only [intervalSegment_zero_one,Path.source,Path.target]
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]

theorem HasFiniteAffineCover.trans {a b c : Plane} {γ : Path a b} {η : Path b c}
    (hγ : HasFiniteAffineCover γ) (hη : HasFiniteAffineCover η) : HasFiniteAffineCover (γ.trans η) := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  obtain ⟨T,hTlt,hTcov,hTaff⟩ := hη
  let L : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalLeft ab.1,intervalLeft ab.2)
  let R : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalRight ab.1,intervalRight ab.2)
  refine ⟨S.image L ∪ T.image R,?_,?_,?_⟩
  · intro ab hab
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalLeft_strictMono (hSlt cd hcd)
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalRight_strictMono (hTlt cd hcd)
  · intro t
    by_cases ht : t.val ≤ 1/2
    · let u : unitInterval := ⟨2*t.val,by constructor <;> linarith [t.property.1]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hScov u
      have hu : intervalLeft u=t := by apply Subtype.ext; change (2*t.val)/2=t.val; ring
      refine ⟨L ab,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalLeft ab.1 ≤ t
        rw [← hu]
        exact intervalLeft_strictMono.monotone ha
      · change t ≤ intervalLeft ab.2
        rw [← hu]
        exact intervalLeft_strictMono.monotone hb
    · let u : unitInterval := ⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hTcov u
      have hu : intervalRight u=t := by apply Subtype.ext; change (1+(2*t.val-1))/2=t.val; ring
      refine ⟨R ab,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalRight ab.1 ≤ t
        rw [← hu]
        exact intervalRight_strictMono.monotone ha
      · change t ≤ intervalRight ab.2
        rw [← hu]
        exact intervalRight_strictMono.monotone hb
  · intro ab hab t
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalLeft cd.1) (intervalLeft cd.2) t)=_
      rw [intervalSegment_left,path_trans_intervalLeft]
      exact (hSaff cd hcd t).trans (by simp only [L,path_trans_intervalLeft])
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalRight cd.1) (intervalRight cd.2) t)=_
      rw [intervalSegment_right,path_trans_intervalRight]
      exact (hTaff cd hcd t).trans (by simp only [R,path_trans_intervalRight])

theorem HasFiniteAffineCover.cast {a b c d : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) (ha : c=a) (hb : d=b) : HasFiniteAffineCover (γ.cast ha hb) := hγ

theorem polygonalArcPath_hasFiniteAffineCover (v : ℕ → Plane) :
    (k : ℕ) → HasFiniteAffineCover (polygonalArcPath v k)
  | 0 => hasFiniteAffineCover_refl _
  | 1 => hasFiniteAffineCover_segment _ _
  | k+2 => (polygonalArcPath_hasFiniteAffineCover v (k+1)).trans (hasFiniteAffineCover_segment _ _)

theorem PolygonalChain.hasFiniteAffineCover {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) : HasFiniteAffineCover P.path :=
  (polygonalArcPath_hasFiniteAffineCover P.vertices P.pieces).cast P.first.symm P.last.symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_PolygonalNormalization
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem alternatingPath_hasFiniteAffineCover (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) (hp : ∀ i, HasFiniteAffineCover (p i))
    (hq : ∀ i, HasFiniteAffineCover (q i)) :
    (k : ℕ) → HasFiniteAffineCover (alternatingPath a b p q k)
  | 0 => hp 0
  | k+1 => ((alternatingPath_hasFiniteAffineCover a b p q hp hq k).trans (hq k)).trans (hp (k+1))

namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middlePath_hasFiniteAffineCover (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    HasFiniteAffineCover (E.middlePath e) :=
  alternatingPath_hasFiniteAffineCover _ _ _ _ (fun i => (E.chain (C.orderedArc e i)).hasFiniteAffineCover)
    (fun _ => hasFiniteAffineCover_segment _ _) _

theorem assembledEdge_hasFiniteAffineCover (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (e : BipartiteEdge m n) :
    HasFiniteAffineCover (E.assembledEdge v e) := by
  apply HasFiniteAffineCover.trans
  · apply HasFiniteAffineCover.trans (hasFiniteAffineCover_segment _ _)
    exact E.middlePath_hasFiniteAffineCover e
  · simp only [endSpoke,Path.segment_symm]
    exact hasFiniteAffineCover_segment _ _

end PolygonalExterior

theorem finite_intersection_normalization_oai {m n : ℕ} (D : FiniteIntersectionDrawing m n) :
    ∃ D' : AdmissibleDrawing m n,
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ crossingCount D' ≤ finiteCrossingCount D := by
  obtain ⟨C⟩ := nonempty_drawingPassages D
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembledEdge_hasFiniteAffineCover v,
    E.assembled_crossingCount_le v hvinj hv hdet⟩

end Zarankiewicz

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.finite_intersection_normalization_oai := @OAI.Zarankiewicz.finite_intersection_normalization_oai

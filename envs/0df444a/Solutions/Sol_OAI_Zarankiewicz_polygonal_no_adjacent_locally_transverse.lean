-- Prove2me | solution 1 for OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:22:01.523548+00:00
-- url     : https://prove2.me/submissions/cfa8f217-8341-4657-8804-edd98535c2ea

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BipartiteCrossing
import Definitions.Def_OAIB3Zr002
import Definitions.Def_OAIB3Zr003
import Theorems.Thm_OAI_Zarankiewicz_finite_intersection_normalization
import Theorems.Thm_OAI_Zarankiewicz_nonempty_polygonalExterior

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
-- module Solutions.OAIB3_Zar.Crossing_FiniteIntersectionDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finiteCrossingCount_eq_ncard {m n : ℕ} (D : FiniteIntersectionDrawing m n) :
    finiteCrossingCount D=(crossingPoints D.toContinuousDrawing).ncard :=
  (Set.ncard_eq_toFinset_card _ D.crossings_finite).symm

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
-- module Solutions.OAIB3_Zar.Crossing_IntervalSegmentStrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem intervalSegment_strict_between (a b t : unitInterval) (hab : a < b)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    a < intervalSegment a b t ∧ intervalSegment a b t < b := by
  have hab' : a.val < b.val := hab
  have ht0 : 0 < t.val := ht.1
  have ht1 : t.val < 1 := ht.2
  have h₀ := mul_pos ht0 (sub_pos.mpr hab')
  have h₁ := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hab')
  change a.val < (1-t.val)*a.val+t.val*b.val ∧ (1-t.val)*a.val+t.val*b.val < b.val
  constructor <;> nlinarith

end Zarankiewicz

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
-- module Solutions.OAIB3_Zar.Crossing_AffineIntervalRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem intervalSegment_interpolate (a b u v t : unitInterval) :
    intervalSegment (intervalSegment a b u) (intervalSegment a b v) t=
      intervalSegment a b (intervalSegment u v t) := by
  apply Subtype.ext
  dsimp [intervalSegment]
  ring

theorem segmentPoint_interpolate (a b : Plane) (u v t : ℝ) :
    segmentPoint (segmentPoint a b u) (segmentPoint a b v) t=
      segmentPoint a b ((1-t)*u+t*v) := by
  ext <;> dsimp [segmentPoint] <;> ring

theorem path_affine_restrict {a b : Plane} (γ : Path a b) (l r : unitInterval) (hlr : l < r)
    (haff : ∀ t : unitInterval, γ (intervalSegment l r t)=segmentPoint (γ l) (γ r) t.val)
    (u v : unitInterval) (hu : l ≤ u ∧ u ≤ r) (hv : l ≤ v ∧ v ≤ r) (t : unitInterval) :
    γ (intervalSegment u v t)=segmentPoint (γ u) (γ v) t.val := by
  obtain ⟨u',rfl⟩ := intervalSegment_surjective_interval l r hlr u hu
  obtain ⟨v',rfl⟩ := intervalSegment_surjective_interval l r hlr v hv
  rw [intervalSegment_interpolate,haff,haff,haff,segmentPoint_interpolate]
  rfl

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrderedAffineSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem strictMono_no_between_successors {k : ℕ} (t : Fin (k+1) → unitInterval)
    (ht : StrictMono t) (i : Fin k) (j : Fin (k+1)) :
    ¬ (t i.castSucc < t j ∧ t j < t i.succ) := by
  intro h
  have hlo : i.castSucc < j := by
    by_contra hn
    exact h.1.not_ge (ht.monotone (le_of_not_gt hn))
  have hhi : j < i.succ := by
    by_contra hn
    exact h.2.not_ge (ht.monotone (le_of_not_gt hn))
  change i.val < j.val at hlo
  change j.val < i.val+1 at hhi
  omega

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AffineSubdivisionRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem HasFiniteAffineCover.refine {a b : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) (R : Finset unitInterval) :
    ∃ P : PolygonalParametrization γ, (R : Set unitInterval) ⊆ Set.range P.knot := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  let T : Finset unitInterval := insert 0 (insert 1 ((S.image Prod.fst ∪ S.image Prod.snd) ∪ R))
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.1 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩))))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.2 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩))))
  have haff : ∀ i : Fin k, ∀ u : unitInterval,
      γ (intervalSegment (t i.castSucc) (t i.succ) u)=segmentPoint (γ (t i.castSucc)) (γ (t i.succ)) u.val := by
    intro i u
    let mid : unitInterval := ⟨1/2,by norm_num⟩
    let z := intervalSegment (t i.castSucc) (t i.succ) mid
    have hz : t i.castSucc < z ∧ z < t i.succ :=
      intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
        constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
    obtain ⟨ab,hab,ha,hb⟩ := hScov z
    have hlo : ab.1 ≤ t i.castSucc := by
      by_contra hn
      obtain ⟨j,hj⟩ := hleft ab hab
      exact strictMono_no_between_successors t ht i j
        ⟨by rw [hj]; exact lt_of_not_ge hn,by rw [hj]; exact ha.trans_lt hz.2⟩
    have hhi : t i.succ ≤ ab.2 := by
      by_contra hn
      obtain ⟨j,hj⟩ := hright ab hab
      exact strictMono_no_between_successors t ht i j
        ⟨by rw [hj]; exact hz.1.trans_le hb,by rw [hj]; exact lt_of_not_ge hn⟩
    have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
    exact path_affine_restrict γ ab.1 ab.2 (hSlt ab hab) (hSaff ab hab)
      (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u
  refine ⟨{pieces:=k,knot:=t,increasing:=ht,first:=h0,last:=h1,affine:=haff},?_⟩
  intro u hu
  change u ∈ Set.range t
  rw [hR]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hu))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SubdivisionSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

theorem pieceTrace_knot_endpoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : Fin P.pieces) (j : Fin (P.pieces+1))
    (hx : γ (P.knot j) ∈ P.pieceTrace i) :
    γ (P.knot j)=γ (P.knot i.castSucc) ∨ γ (P.knot j)=γ (P.knot i.succ) := by
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter i _ hx
  by_cases ht0 : t=0
  · subst t
    simpa [intervalSegment] using Or.inl ht.symm
  by_cases ht1 : t=1
  · subst t
    simpa [intervalSegment] using Or.inr ht.symm
  have hmid := intervalSegment_strict_between (P.knot i.castSucc) (P.knot i.succ) t
    (P.increasing (by change i.val < i.val+1; omega))
    ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
  have he := hγ ht
  rw [he] at hmid
  exact False.elim (strictMono_no_between_successors P.knot P.increasing i j hmid)

theorem pieceTrace_other_piece_endpoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i j : Fin P.pieces) (hij : i ≠ j) (x : Plane)
    (hx : x ∈ P.pieceTrace i) (hy : x ∈ P.pieceTrace j) :
    x=γ (P.knot i.castSucc) ∨ x=γ (P.knot i.succ) := by
  obtain ⟨s,hs⟩ := P.pieceTrace_parameter i x hx
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter j x hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl (by simpa [intervalSegment] using hs.symm)
  by_cases hs1 : s=1
  · subst s
    exact Or.inr (by simpa [intervalSegment] using hs.symm)
  have hsbetween := intervalSegment_strict_between (P.knot i.castSucc) (P.knot i.succ) s
    (P.increasing (by change i.val < i.val+1; omega))
    ⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩
  have htbetween := intervalSegment_between (P.knot j.castSucc) (P.knot j.succ) t
    (P.increasing.monotone (by change j.val ≤ j.val+1; omega))
  have he := hγ (hs.trans ht.symm)
  rw [he] at hsbetween
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hgap := P.increasing.monotone (show i.succ ≤ j.castSucc by change i.val+1 ≤ j.val; exact hij)
    exact False.elim (hsbetween.2.not_ge (hgap.trans htbetween.1))
  · have hgap := P.increasing.monotone (show j.succ ≤ i.castSucc by change j.val+1 ≤ i.val; exact hji)
    exact False.elim (hsbetween.1.not_ge (htbetween.2.trans hgap))

end Zarankiewicz.PolygonalParametrization
namespace Zarankiewicz
variable {m n : ℕ}

theorem subdivision_mark_endpoint (D : AdmissibleDrawing m n)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (e : BipartiteEdge m n) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ (P e).pieceTrace i) (hm : x ∈ drawingMarks D.toFiniteIntersectionDrawing) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hmark e t (ht.symm ▸ hm)
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingSegmentIncidence
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem drawing_curve_meeting_mark (D : AdmissibleDrawing m n) (e f : BipartiteEdge m n)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hy : x ∈ Set.range (D.edge f)) :
    x ∈ drawingMarks D.toFiniteIntersectionDrawing := by
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl ⟨.inl e.1,by simpa using hs⟩
  by_cases hs1 : s=1
  · subst s
    exact Or.inl ⟨.inr e.2,by simpa using hs⟩
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨.inl f.1,by simpa using ht⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inl ⟨.inr f.2,by simpa using ht⟩
  exact Or.inr ⟨e,f,hef,
    ⟨s,⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩,hs⟩,
    ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,ht⟩⟩

theorem drawing_pieces_meeting_endpoints (D : AdmissibleDrawing m n)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (p q : DrawingPiece P) (hpq : p ≠ q) (x : Plane)
    (hx : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p))
    (hy : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q)) :
    (x=drawingPieceStart P p ∨ x=drawingPieceEnd P p) ∧
      (x=drawingPieceStart P q ∨ x=drawingPieceEnd P q) := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  by_cases hef : e=f
  · subst f
    have hij : i ≠ j := fun he => hpq (by subst j; rfl)
    exact ⟨(P e).pieceTrace_other_piece_endpoint (D.edge_injective e) i j hij x hx hy,
      (P e).pieceTrace_other_piece_endpoint (D.edge_injective e) j i (Ne.symm hij) x hy hx⟩
  · have hm := drawing_curve_meeting_mark D e f hef x
      ((P e).pieceTrace_subset_range i hx) ((P f).pieceTrace_subset_range j hy)
    exact ⟨subdivision_mark_endpoint D P hmark e i x hx hm,
      subdivision_mark_endpoint D P hmark f j x hy hm⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_DrawingSubdivisionGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem common_endpoint_alternatives (a b c d x : Plane) (hab : x=a ∨ x=b) (hcd : x=c ∨ x=d) :
    (a=c ∧ x=a) ∨ (a=d ∧ x=a) ∨ (b=c ∧ x=b) ∨ (b=d ∧ x=b) := by
  rcases hab with ha | hb <;> rcases hcd with hc | hd
  · exact Or.inl ⟨ha.symm.trans hc,ha⟩
  · exact Or.inr (Or.inl ⟨ha.symm.trans hd,ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb.symm.trans hc,hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb.symm.trans hd,hb⟩))

theorem drawingSubdivisionGraph_embedding (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) :
    StraightEdgeEmbedding (drawingSubdivisionGraph P) id := by
  refine ⟨Function.injective_id,?_⟩
  rintro a b c d ⟨hab,p,hp⟩ ⟨hcd,q,hq⟩ x hx hy
  by_cases hpq : p=q
  · subst q
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inl ⟨rfl,rfl⟩
  · have hxp : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx
      · simpa only [id_eq,segment_symm] using hx
    have hxq : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q) := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hy
      · simpa only [id_eq,segment_symm] using hy
    obtain ⟨hpe,hqe⟩ := drawing_pieces_meeting_endpoints D P hmark p q hpq x hxp hxq
    have heab : x=a ∨ x=b := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hpe
      · exact hpe.symm
    have hecd : x=c ∨ x=d := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hqe
      · exact hqe.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives a b c d x heab hecd))

end Zarankiewicz

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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ExtraDrawingSubdivision
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem exists_drawing_subdivision_at (D : AdmissibleDrawing m n)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) (S : Set Plane) (hS : S.Finite) :
    ∃ P : ∀ e, PolygonalParametrization (D.edge e),
      (∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) ∧
      (∀ e t, D.edge e t ∈ S → t ∈ Set.range (P e).knot) := by
  classical
  have hfinite (e : BipartiteEdge m n) : ((D.edge e) ⁻¹' (drawingMarks D.toFiniteIntersectionDrawing ∪ S)).Finite :=
    ((drawingMarks_finite D.toFiniteIntersectionDrawing).union hS).preimage (D.edge_injective e).injOn
  have hex (e : BipartiteEdge m n) := (hpoly e).refine (hfinite e).toFinset
  choose P hP using hex
  refine ⟨P,?_,?_⟩
  · intro e t ht
    exact hP e (by simpa using Or.inl ht)
  · intro e t ht
    exact hP e (by simpa using Or.inr ht)

namespace PolygonalExterior
variable {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_assembled_port_subdivision (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    ∃ P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e),
      (∀ e t, E.assembledEdge v e t ∈ drawingMarks (E.assembledAdmissible v hvinj hv hdet).toFiniteIntersectionDrawing →
        t ∈ Set.range (P e).knot) ∧
      (∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot) :=
  exists_drawing_subdivision_at (E.assembledAdmissible v hvinj hv hdet)
    (E.assembledEdge_hasFiniteAffineCover v) (Set.range C.portPoint) (Set.finite_range _)

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrderedPathParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem OrderedPathPart.refl {a b : Plane} (γ : Path a b) : OrderedPathPart γ γ :=
  ⟨id,strictMono_id,fun _ => rfl⟩

theorem OrderedPathPart.trans {a b c d e f : Plane} {γ : Path a b} {δ : Path c d} {η : Path e f}
    (hγ : OrderedPathPart γ δ) (hδ : OrderedPathPart δ η) : OrderedPathPart γ η := by
  obtain ⟨u,hu,he⟩ := hγ
  obtain ⟨v,hv,hf⟩ := hδ
  exact ⟨u ∘ v,hu.comp hv,fun t => (he (v t)).trans (hf t)⟩

theorem OrderedPathPart.left {a b c d e : Plane} {γ : Path a b} {δ : Path d e}
    (h : OrderedPathPart γ δ) (η : Path b c) : OrderedPathPart (γ.trans η) δ :=
  (show OrderedPathPart (γ.trans η) γ from
    ⟨intervalLeft,intervalLeft_strictMono,path_trans_intervalLeft γ η⟩).trans h

theorem OrderedPathPart.right {a b c d e : Plane} {γ : Path b c} {δ : Path d e}
    (h : OrderedPathPart γ δ) (η : Path a b) : OrderedPathPart (η.trans γ) δ :=
  (show OrderedPathPart (η.trans γ) γ from
    ⟨intervalRight,intervalRight_strictMono,path_trans_intervalRight η γ⟩).trans h

theorem OrderedPathPart.congr_right {a b c d e f : Plane} {γ : Path a b}
    {δ : Path c d} {η : Path e f} (h : OrderedPathPart γ δ) (he : ∀ t, δ t=η t) :
    OrderedPathPart γ η := by
  obtain ⟨u,hu,hh⟩ := h
  exact ⟨u,hu,fun t => (hh t).trans (he t)⟩

theorem OrderedPathPart.endpoints_ordered {a b c d : Plane} {γ : Path a b} {δ : Path c d}
    (h : OrderedPathPart γ δ) :
    ∃ u v : unitInterval, u < v ∧ γ u=c ∧ γ v=d := by
  obtain ⟨f,hf,he⟩ := h
  exact ⟨f 0,f 1,hf zero_lt_one,(he 0).trans δ.source,(he 1).trans δ.target⟩

theorem alternatingPath_contains_bridge (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) :
    (n : ℕ) → ∀ i, i < n → OrderedPathPart (alternatingPath a b p q n) (q i)
  | 0, i, hi => by omega
  | n+1, i, hi => by
    by_cases he : i=n
    · subst i
      exact ((OrderedPathPart.refl (q n)).right _).left _
    · exact ((alternatingPath_contains_bridge a b p q n i (by omega)).left (q n)).left (p (n+1))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_OrderedCrossingPorts
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem middlePath_contains_chord (E : PolygonalExterior C) (p : C.InnerIndex) :
    OrderedPathPart (E.middlePath p.1) (C.crossingChord p) := by
  rcases p with ⟨e,⟨i,hi⟩⟩
  have hj : i.val-1+1 < C.count e := by omega
  have hinner : C.orderedInner e (i.val-1) hj=⟨e,⟨i,hi⟩⟩ := by
    unfold DrawingPassages.orderedInner
    congr 1
    apply Subtype.ext
    apply Fin.ext
    change i.val-1+1=i.val
    omega
  have hpart : OrderedPathPart (E.middlePath e) (orderedBridge C e (i.val-1)) :=
    alternatingPath_contains_bridge _ _ _ _ (C.count e-1) (i.val-1) (by omega)
  apply hpart.congr_right
  intro t
  rw [orderedBridge_apply (C:=C) e (i.val-1) hj t,hinner]

theorem assembledEdge_contains_chord (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (p : C.InnerIndex) :
    OrderedPathPart (E.assembledEdge v p.1) (C.crossingChord p) := by
  have h : OrderedPathPart (E.anchoredMiddle p.1) (C.crossingChord p) := E.middlePath_contains_chord p
  exact (h.right (startSpoke C v p.1)).left (endSpoke C v p.1)

theorem assembled_crossing_ports_ordered (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (p : C.InnerIndex) :
    ∃ u w : unitInterval, u < w ∧
      E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p) ∧
      E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p) :=
  (E.assembledEdge_contains_chord v p).endpoints_ordered

theorem crossing_port_walk_indices (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p : C.InnerIndex) :
    ∃ i j : Fin ((P p.1).pieces+1), i < j ∧
      (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p) ∧
      (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p) := by
  obtain ⟨u,w,huw,hu,hw⟩ := E.assembled_crossing_ports_ordered v p
  obtain ⟨i,hi⟩ := hport p.1 u ⟨C.incomingPort p,hu.symm⟩
  obtain ⟨j,hj⟩ := hport p.1 w ⟨C.outgoingPort p,hw.symm⟩
  have hij : i < j := by
    by_contra hn
    have hh := (P p.1).increasing.monotone (le_of_not_gt hn)
    rw [hi,hj] at hh
    exact huw.not_ge hh
  refine ⟨i,j,hij,?_,?_⟩
  · rw [drawingEdgeWalk_getVert P p.1 i.val (by omega)]
    have he := (P p.1).vertices_at i
    change (P p.1).vertices i.val=E.assembledEdge v p.1 ((P p.1).knot i) at he
    exact he.trans ((congrArg (E.assembledEdge v p.1) hi).trans hu)
  · rw [drawingEdgeWalk_getVert P p.1 j.val (by omega)]
    have he := (P p.1).vertices_at j
    change (P p.1).vertices j.val=E.assembledEdge v p.1 ((P p.1).knot j) at he
    exact he.trans ((congrArg (E.assembledEdge v p.1) hj).trans hw)

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingPortClearance
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace DrawingPassages
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem crossingChord_parameter_interior (C : DrawingPassages D.toFiniteIntersectionDrawing) (p : C.InnerIndex)
    (t : unitInterval) (ht : C.crossingChord p t ∈ C.crossingDisk p) :
    t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 0-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.source,C.incomingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 1-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.target,C.outgoingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_crossing_disk_parameter_between (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : E.assembledEdge v p.1 t ∈ C.crossingDisk p) : u < t ∧ t < w := by
  obtain ⟨f,hf,he⟩ := E.assembledEdge_contains_chord v p
  have h0 : f 0=u := E.assembledEdge_injective v hv p.1
    (((he 0).trans (C.crossingChord p).source).trans hu.symm)
  have h1 : f 1=w := E.assembledEdge_injective v hv p.1
    (((he 1).trans (C.crossingChord p).target).trans hw.symm)
  have hmem : E.assembledEdge v p.1 t ∈ Set.range (C.crossingChord p) :=
    (E.assembled_range_in_crossingDisk v hv p _ ht).mp ⟨t,rfl⟩
  obtain ⟨s,hs⟩ := hmem
  have hsint := C.crossingChord_parameter_interior p s (hs.symm ▸ ht)
  have hst : f s=t := E.assembledEdge_injective v hv p.1 ((he s).trans hs)
  exact ⟨by simpa only [h0,hst] using hf hsint.1,by simpa only [h1,hst] using hf hsint.2⟩

theorem assembled_crossing_port_clearance (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : t ≤ u ∨ w ≤ t) : E.assembledEdge v p.1 t ∉ C.crossingDisk p := by
  intro hmem
  have hbetween := E.assembled_crossing_disk_parameter_between v hv p u w hu hw t hmem
  rcases ht with ht | ht
  · exact hbetween.1.not_ge ht
  · exact hbetween.2.not_ge ht

end PolygonalExterior
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingCutWalks
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem crossing_cut_traces_disjoint (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (p : C.InnerIndex) (i j : Fin ((P p.1).pieces+1))
    (hi : (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p))
    (hj : (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p)) :
    Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take i.val))) (C.crossingDisk p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop j.val))) (C.crossingDisk p) := by
  have hki : (drawingEdgeWalk P p.1).getVert i.val=E.assembledEdge v p.1 ((P p.1).knot i) :=
    (drawingEdgeWalk_getVert P p.1 i.val (by omega)).trans ((P p.1).vertices_at i)
  have hkj : (drawingEdgeWalk P p.1).getVert j.val=E.assembledEdge v p.1 ((P p.1).knot j) :=
    (drawingEdgeWalk_getVert P p.1 j.val (by omega)).trans ((P p.1).vertices_at j)
  have hu := hki.symm.trans hi
  have hw := hkj.symm.trans hj
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hxin
    obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P p.1 i hx
    exact E.assembled_crossing_port_clearance v hv p _ _ hu hw t (Or.inl ht.2) (he.symm ▸ hxin)
  · apply Set.disjoint_left.mpr
    intro x hx hxin
    obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P p.1 j hx
    exact E.assembled_crossing_port_clearance v hv p _ _ hu hw t (Or.inr ht.1) (he.symm ▸ hxin)

theorem exists_exterior_crossing_cuts (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p : C.InnerIndex) :
    ∃ i j : Fin ((P p.1).pieces+1), i < j ∧
      (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p) ∧
      (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take i.val))) (C.crossingDisk p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop j.val))) (C.crossingDisk p) := by
  obtain ⟨i,j,hij,hi,hj⟩ := E.crossing_port_walk_indices v hvinj hv hdet P hport p
  exact ⟨i,j,hij,hi,hj,E.crossing_cut_traces_disjoint v hvinj hv hdet P p i j hi hj⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SegmentAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exterior_segment_chord_meeting (G : SimpleGraph Plane) (U : Set Plane) (a b x y z : Plane)
    (hxy : G.Adj x y) (hout : ∀ x y, G.Adj x y → Disjoint (segment ℝ x y) U)
    (hin : openSegmentTrace a b ⊆ U)
    (ha : a ∈ segment ℝ x y → a=x ∨ a=y) (hb : b ∈ segment ℝ x y → b=x ∨ b=y)
    (hz : z ∈ segment ℝ x y) (hchord : z ∈ segment ℝ a b) :
    (z=x ∨ z=y) ∧ (z=a ∨ z=b) := by
  rcases segment_endpoint_or_open a b z hchord with rfl | rfl | hz'
  · exact ⟨ha hz,Or.inl rfl⟩
  · exact ⟨hb hz,Or.inr rfl⟩
  · exact False.elim (Set.disjoint_left.mp (hout x y hxy) hz (hin hz'))

theorem segmentAugmentedGraph_embedding {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) (hemb : StraightEdgeEmbedding G id) (U : Set Plane)
    (hout : ∀ x y, G.Adj x y → Disjoint (segment ℝ x y) U)
    (hin : ∀ i, openSegmentTrace (a i) (b i) ⊆ U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (segment ℝ (a i) (b i)) (segment ℝ (a j) (b j)))
    (hend : ∀ i x y, G.Adj x y →
      (a i ∈ segment ℝ x y → a i=x ∨ a i=y) ∧
      (b i ∈ segment ℝ x y → b i=x ∨ b i=y)) :
    StraightEdgeEmbedding (segmentAugmentedGraph G a b hne) id := by
  refine ⟨Function.injective_id,?_⟩
  intro x y z w hxy hzw r hrx hrz
  rcases hxy with hxy | ⟨i,hi⟩ <;> rcases hzw with hzw | ⟨j,hj⟩
  · exact hemb.2 x y z w hxy hzw r hrx hrz
  · have hchord : r ∈ segment ℝ (a j) (b j) := by
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hrz
      · simpa only [id_eq,segment_symm] using hrz
    obtain ⟨hold,hnew⟩ := exterior_segment_chord_meeting G U (a j) (b j) x y r hxy hout
      (hin j) (hend j x y hxy).1 (hend j x y hxy).2 hrx hchord
    have hrzw : r=z ∨ r=w := by
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact hnew.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives x y z w r hold hrzw))
  · have hchord : r ∈ segment ℝ (a i) (b i) := by
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hrx
      · simpa only [id_eq,segment_symm] using hrx
    obtain ⟨hold,hnew⟩ := exterior_segment_chord_meeting G U (a i) (b i) z w r hzw hout
      (hin i) (hend i z w hzw).1 (hend i z w hzw).2 hrz hchord
    have hrxy : r=x ∨ r=y := by
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact hnew.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives x y z w r hrxy hold))
  · by_cases hij : i=j
    · subst j
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inl ⟨rfl,rfl⟩
    · apply False.elim
      apply Set.disjoint_left.mp (hdisj i j hij)
      · rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hrx
        · simpa only [id_eq,segment_symm] using hrx
      · rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hrz
        · simpa only [id_eq,segment_symm] using hrz

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SubdivisionPointEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem subdivision_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (e : BipartiteEdge m n) (i : Fin (P e).pieces) (hx : x ∈ (P e).pieceTrace i) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hpoint e t ht
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh

theorem drawingSubdivisionGraph_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (a b : Plane) (hab : (drawingSubdivisionGraph P).Adj a b) (hx : x ∈ segment ℝ a b) :
    x=a ∨ x=b := by
  obtain ⟨hab,p,hp⟩ := hab
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact subdivision_point_endpoint P x hpoint p.1 p.2 hx
  · have hx' : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      simpa only [segment_symm] using hx
    exact (subdivision_point_endpoint P x hpoint p.1 p.2 hx').symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_CrossingSurgeryGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

theorem crossingSurgeryGraph_embedding (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e))
    (hmark : ∀ e t, D'.edge e t ∈ drawingMarks D'.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (hport : ∀ e t, D'.edge e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p q : C.InnerIndex) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id := by
  have hemb := drawingSubdivisionGraph_embedding P hmark
  have houtEmb : StraightEdgeEmbedding
      (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p)) id := by
    refine ⟨hemb.1,?_⟩
    intro a b c d hab hcd x hx hy
    exact hemb.2 a b c d hab.1 hcd.1 x hx hy
  apply segmentAugmentedGraph_embedding _ _ _ _ houtEmb (C.crossingDisk p)
  · intro x y hxy
    exact hxy.2
  · exact C.reconnection_open_in_disk p q hm
  · exact C.reconnection_chords_disjoint p q hcross
  · intro i x y hxy
    constructor
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.incomingPort q,ht.symm⟩
      · exact ⟨C.incomingPort p,ht.symm⟩
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.outgoingPort p,ht.symm⟩
      · exact ⟨C.outgoingPort q,ht.symm⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_ExteriorCrossingCut
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

theorem PolygonalExterior.nonempty_exteriorCrossingCut {C : DrawingPassages D.toFiniteIntersectionDrawing} (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (r : C.InnerIndex) : Nonempty (ExteriorCrossingCut C P r) := by
  obtain ⟨i,j,hij,hi,hj,hout,hout'⟩ := E.exists_exterior_crossing_cuts v hvinj hv hdet P hport r
  exact ⟨⟨i,j,hij,hi,hj,hout,hout'⟩⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_SurgeryFiniteDrawing
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryFiniteDrawing_count_lt
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    finiteCrossingCount (E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq) <
      crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  rw [finiteCrossingCount_eq_ncard]
  have h := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).2
  exact h.trans_eq (Set.ncard_eq_toFinset_card _ (E.assembledAdmissible v hvinj hv hdet).crossings_finite)

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_AdmissibleAdjacentSurgery
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_admissible_adjacent_surgery (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    ∃ A : AdmissibleDrawing m n, (∀ e, HasFiniteAffineCover (A.edge e)) ∧
      crossingCount A < crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  obtain ⟨P,hmark,hport⟩ := E.exists_assembled_port_subdivision v hvinj hv hdet
  obtain ⟨Kp⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport p
  obtain ⟨Kq⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport q
  have hemb := crossingSurgeryGraph_embedding C P hmark hport p q hm hcross
  let B := E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq
  obtain ⟨A,hpoly,hcount⟩ := finite_intersection_normalization B
  exact ⟨A,hpoly,hcount.trans_lt
    (E.adjacentSurgeryFiniteDrawing_count_lt v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq)⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_LocallyStraightNormalization
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

namespace PolygonalExterior
variable {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_locallyStraightCrossings (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    LocallyStraightCrossings (E.assembledAdmissible v hvinj hv hdet) := by
  intro e f hef x hx hy
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hpx := (C.crossingChord_meeting_proper p q hpq x hxp hxq).1
  have hqx := (C.crossingChord_meeting_proper q p (Ne.symm hpq) x hxq hxp).1
  have hlocal (r : C.InnerIndex) (hr : x ∈ C.crossingDisk r)
      (hxr : x ∈ Set.range (C.crossingChord r)) :
      LocallyStraightAt (E.assembledDrawing v hvinj hv) r.1 x := by
    refine ⟨C.portPoint (C.incomingPort r),C.portPoint (C.outgoingPort r),
      C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort r r),
      (C.crossingChord_openTrace_iff r x hr).mp hxr,C.crossingDisk r,C.crossingDisk_isOpen r,hr,?_⟩
    exact E.assembled_trace_in_crossingDisk v hvinj hv r
  change LocallyStraightAt (E.assembledDrawing v hvinj hv) e x ∧
    LocallyStraightAt (E.assembledDrawing v hvinj hv) f x
  exact ⟨by simpa only [hp] using hlocal p hpx hxp,by simpa only [hq] using hlocal q hqx hxq⟩

end PolygonalExterior

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_NoAdjacentNormalization
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_no_adjacent_assembled {m n : ℕ} (D : AdmissibleDrawing m n) :
    ∃ (B : AdmissibleDrawing m n) (C : DrawingPassages B.toFiniteIntersectionDrawing)
      (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
      (hv : ∀ j, squaredLength (v j-B.vertex j) < C.radius^2)
      (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
        det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0),
      NoAdjacentCrossings (E.assembledAdmissible v hvinj hv hdet) ∧
        crossingCount (E.assembledAdmissible v hvinj hv hdet) ≤ crossingCount D := by
  classical
  induction hc : crossingCount D using Nat.strong_induction_on generalizing D with
  | h k ih =>
    obtain ⟨C⟩ := nonempty_drawingPassages D.toFiniteIntersectionDrawing
    obtain ⟨E⟩ := nonempty_polygonalExterior C
    obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
    let A := E.assembledAdmissible v hvinj hv hdet
    have hcount : crossingCount A ≤ crossingCount D := E.assembled_crossingCount_le v hvinj hv hdet
    by_cases hnorm : NoAdjacentCrossings A
    · exact ⟨D,C,E,v,hvinj,hv,hdet,hnorm,hcount.trans_eq hc⟩
    have hex : ∃ e f : BipartiteEdge m n, e ≠ f ∧ (e.1=f.1 ∨ e.2=f.2) ∧
        (edgeInterior A.toContinuousDrawing e ∩ edgeInterior A.toContinuousDrawing f).Nonempty := by
      by_contra hh
      apply hnorm
      intro e f hef hadj
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hh ⟨e,f,hef,hadj,x,hx⟩
    obtain ⟨e,f,hef,hadj,x,hxe,hxf⟩ := hex
    obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
      (edgeInterior_not_vertex A.toContinuousDrawing e x hxe)
      (edgeInterior_subset_range A.toContinuousDrawing e hxe)
      (edgeInterior_subset_range A.toContinuousDrawing f hxf)
    have hpq : p ≠ q := fun h => hef (hp.symm.trans ((congrArg Sigma.fst h).trans hq))
    have hadj' : p.1.1=q.1.1 ∨ p.1.2=q.1.2 := by simpa only [hp,hq] using hadj
    obtain ⟨R,hRpoly,hRcount⟩ := E.exists_admissible_adjacent_surgery v hvinj hv hdet p q hpq hadj' x hxp hxq
    have hRk : crossingCount R < k := (hRcount.trans_le hcount).trans_eq hc
    obtain ⟨B,C',E',v',hvinj',hv',hdet',hnorm',hcount'⟩ := ih (crossingCount R) hRk R rfl
    exact ⟨B,C',E',v',hvinj',hv',hdet',hnorm',(hcount'.trans (hRcount.le.trans hcount)).trans_eq hc⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIB3_Zar.Crossing_LocallyTransverseNormalization
attribute [-instance] _root_.OAI.Zarankiewicz.incidentEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem DrawingPassages.crossingChord_meeting_det {D : FiniteIntersectionDrawing m n}
    (C : DrawingPassages D) (p q : C.InnerIndex) (hpq : p ≠ q)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    det2 (C.portPoint (C.outgoingPort p)-C.portPoint (C.incomingPort p))
      (C.portPoint (C.outgoingPort q)-C.portPoint (C.incomingPort q)) ≠ 0 := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have he : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val =
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [DrawingPassages.crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]
      using hs.trans ht.symm
  exact (C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property he).1

theorem PolygonalExterior.assembled_locallyTransverseCrossings
    {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D} (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    LocallyTransverseCrossings (E.assembledAdmissible v hvinj hv hdet) := by
  intro e f hef x hx hy
  let A := E.assembledAdmissible v hvinj hv hdet
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (edgeInterior_not_vertex A.toContinuousDrawing e x hx)
    (edgeInterior_subset_range A.toContinuousDrawing e hx)
    (edgeInterior_subset_range A.toContinuousDrawing f hy)
  have hpq : p ≠ q := fun h => hef (hp.symm.trans ((congrArg Sigma.fst h).trans hq))
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hxin := (C.crossingChord_meeting_proper p q hpq x hxp hxq).1
  have hxqin := (C.crossingChord_meeting_proper q p (Ne.symm hpq) x hxq hxp).1
  refine ⟨C.portPoint (C.incomingPort p),C.portPoint (C.outgoingPort p),
    C.portPoint (C.incomingPort q),C.portPoint (C.outgoingPort q),
    C.crossingChord_meeting_det p q hpq x hxp hxq,
    (C.crossingChord_openTrace_iff p x hxin).mp hxp,
    (C.crossingChord_openTrace_iff q x hxqin).mp hxq,
    C.crossingDisk p,C.crossingDisk_isOpen p,hxin,?_,?_⟩
  · intro z hz
    change z ∈ edgeInterior (E.assembledDrawing v hvinj hv) e ↔ _
    simpa only [hp] using E.assembled_trace_in_crossingDisk v hvinj hv p z hz
  · intro z hz
    have hzq : z ∈ C.crossingDisk q := by
      change squaredLength (z-(C.innerMark q).val) < C.radius^2
      rw [← hm]
      exact hz
    change z ∈ edgeInterior (E.assembledDrawing v hvinj hv) f ↔ _
    simpa only [hq] using E.assembled_trace_in_crossingDisk v hvinj hv q z hzq

theorem polygonal_no_adjacent_locally_transverse_oai (D : AdmissibleDrawing m n) :
    ∃ A : AdmissibleDrawing m n, crossingCount A ≤ crossingCount D ∧
      (∀ e, HasFiniteAffineCover (A.edge e)) ∧ NoAdjacentCrossings A ∧
      LocallyStraightCrossings A ∧ LocallyTransverseCrossings A := by
  obtain ⟨B,C,E,v,hvinj,hv,hdet,hnorm,hcount⟩ := exists_no_adjacent_assembled D
  exact ⟨E.assembledAdmissible v hvinj hv hdet,hcount,E.assembledEdge_hasFiniteAffineCover v,
    hnorm,E.assembled_locallyStraightCrossings v hvinj hv hdet,
    E.assembled_locallyTransverseCrossings v hvinj hv hdet⟩

end Zarankiewicz

end

end OAI
end

theorem solution : type_of% @OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse_oai := @OAI.Zarankiewicz.polygonal_no_adjacent_locally_transverse_oai
